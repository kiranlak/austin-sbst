(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open Printf
open Options
open Utils

module Log = LogManager

let prototypes : (string, fundec) Hashtbl.t = Hashtbl.create 100000
let globalVariables = ref []

let inputVarinfos : varinfo list ref = ref []

let globalsToIgnore : string list ref = ref ["stdin";"stdout";"stderr"]

let loadGlobalsToIgnoreFromFile (fname:string) = 
	let ic = open_in fname in
	(
		try
	    while true do
	      let line = input_line ic in
				if line <> "" && not(startsWith "--" line) then (
					globalsToIgnore := (ConfigFile.trim line)::!globalsToIgnore;
				)
	    done
	  with End_of_file -> ()
	);
	close_in ic
	
let reset full = 
	Hashtbl.clear prototypes;
	globalVariables := [];
	if full then
		globalsToIgnore := [];
	()
	
let austinGetString = "Austin__Get"

let rec typeToString (prefix : string) (t:typ) =
	match (unrollType t) with
		| TVoid _ -> prefix^"Void"
		| TInt(kind, _) -> prefix^(ikindToString kind)
		| TFloat(kind, _) -> prefix^(fkindToString kind)
		| TPtr(t', _) -> prefix^(typeToString "Ptr__" t')
		| TArray(t', alo, _) -> 
			let length = lenOfArray alo in
			prefix^(typeToString ("Array__"^(string_of_int length)^"__") t')
		| TNamed(ti, _) -> prefix^(typeToString (ti.tname^"__")) ti.ttype
		| TComp(ci, _) -> prefix^ci.cname
		| TEnum(ei, _) -> prefix^ei.ename
		| _ -> 
			Log.unimp (sprintf "Unsupported input type (%s) %s\n" prefix (Pretty.sprint 255 (Cil.d_type () (unrollType t))))
	
let rec removeAllConstAttributes (t:typ) = 
	match t with
		| TVoid(atts) -> TVoid(dropAttribute "const" atts)
		| TInt(kind, atts) -> TInt(kind,(dropAttribute "const" atts))
		| TFloat(kind, atts) -> TFloat(kind,(dropAttribute "const" atts))
		| TPtr(pt, atts) -> 
			let pt' = removeAllConstAttributes pt in
			TPtr(pt', (dropAttribute "const" atts))
		| TArray(at, lopt, atts) -> 
			let at' = removeAllConstAttributes at in
			TArray(at', lopt, (dropAttribute "const" atts))
		| TFun(rt, args, vararg, atts) -> 
			TFun(rt, args, vararg, (dropAttribute "const" atts))
		| TNamed(ti, atts) ->
			let t' = removeAllConstAttributes ti.ttype in
			ti.ttype <- t';
			TNamed(ti, (dropAttribute "const" atts))
		| TComp(ci, atts) -> 
			TComp(ci, (dropAttribute "const" atts))
		| TEnum(ei, atts) -> 
			TEnum(ei, (dropAttribute "const" atts))
		| TBuiltin_va_list(atts) -> 
			TBuiltin_va_list(dropAttribute "const" atts)

let makeLvalInputType (l:lval) = 
	let t = typeOfLval l in
	removeAllConstAttributes t
	
let makeIntTypeCall (kind : ikind) (l : lval) = 
	let f = emptyFunction (austinGetString^(ikindToString kind)^"Value") in
	let t = unrollType (makeLvalInputType l) in
	setFunctionTypeMakeFormals f (TFun(t, 
	Some[("address", voidPtrType, []);("offset", uintType, []);("width", uintType, [])], 
	false, []));
	let addressOf, offset, width = addrAndBitOffset l in
	f.svar.vstorage <- Extern;
	Hashtbl.replace prototypes f.svar.vname f;
	Call(Some(l), Lval((var f.svar)), [addressOf;offset;width], locUnknown)
		
let makeFloatTypeCall (kind : fkind) (l : lval) = 
	let f = emptyFunction (austinGetString^(fkindToString kind)^"Value") in
	let t = unrollType (makeLvalInputType l) in
	setFunctionTypeMakeFormals f (TFun(t, Some[("address", voidPtrType, [])], false, []));
	let addressOf = mkAddrOf l in
	f.svar.vstorage <- Extern;
	Hashtbl.replace prototypes f.svar.vname f;
	Call(Some(l), Lval((var f.svar)), [addressOf], locUnknown)

let generatePointerPostAssignment (pt:typ) = 
	let funcName = typeToString "Austin__postAssign__" pt in
	let f = emptyFunction funcName in
	f.svar.vtype <- (TFun(voidType, Some[("source", voidPtrType, []);("target", voidPtrType, [])], false, []));
	if not(Hashtbl.mem prototypes funcName) then (
		let vsource = makeFormalVar f "source" voidPtrType in
		let vtarget = makeFormalVar f "target" voidPtrType in
		(* implement function body *)
		let sourceType = TPtr(pt, []) in
		let vptr = makeLocalVar f "ptrSource" sourceType in
		let s1 = 
			(* e.g. struct cell** ptrSource = (struct cell** )source;*)
			mkStmt (Instr([Set((var vptr), (mkCast (Lval((var vsource))) sourceType), locUnknown)]))
		in
		let s2 = 
			let ifExp = BinOp(Ne, Lval((var vptr)), (mkCast zero voidPtrType), intType) in
			let thn = 
				let lhs = Mem(Lval(var vptr)),NoOffset in
				let rhs = mkCast (Lval((var vtarget))) (makeLvalInputType lhs) in
				mkBlock [mkStmt (Instr([Set(lhs, rhs, locUnknown)]))]
			in
			let els = mkBlock [] in
			mkStmt (If(ifExp, thn, els, locUnknown))
		in
		f.sbody <- mkBlock [s1;s2];
		Hashtbl.replace prototypes funcName f;
		(* now make a global function pointer *)
		let vFPTR = makeGlobalVar ("funcPtr__"^funcName) (TPtr(f.svar.vtype, [])) in
		globalVariables := ((GVarDecl(vFPTR, locUnknown))::(!globalVariables));
		(f, vFPTR)
	) else (
		(* find global function pointer for var *)
		let vFPTR = "funcPtr__"^funcName in
		let globFPTR =
			List.find (fun g -> match g with GVarDecl(v, _) -> v.vname = vFPTR | _ -> false) (!globalVariables)
		in
		match globFPTR with
			| GVarDecl(v, _) -> ((Hashtbl.find prototypes f.svar.vname), v)
			| _ -> 
				Log.error (sprintf "Failed to get global function pointer %s\n" vFPTR)
	)

let makeAustinPtrCall (l:lval) (argSize : exp) (argProc : exp) (argAddr : exp) (argFunc : exp) = 
	let f = emptyFunction "Austin__GetPtr" in
	setFunctionTypeMakeFormals f (TFun(voidPtrType, 
		Some[("size", uintType, []);
				 ("proc", intPtrType, []);
				 ("address", voidPtrType,[]);
				 ("assignmentFunction", (typeOf argFunc), [])], 
		false, []));
	f.svar.vstorage <- Extern;
	Hashtbl.replace prototypes f.svar.vname f;
	Call(Some(l), Lval((var f.svar)), [argSize;argProc;argAddr;argFunc], locUnknown)

let rec hasVarConstAttr (v:varinfo) = 
	if (hasAttribute "const" v.vattr) then true
	else (hasTypeConstAttr v.vtype)
and hasTypeConstAttr (t:typ) = 
	match t with
		| TVoid(attr) | TInt(_,attr) | TFloat(_,attr) |  TFun(_,_,_,attr) | TComp(_,attr) | TEnum(_,attr) | TBuiltin_va_list(attr) ->  (hasAttribute "const" attr)
		| TArray(at,_,attr) -> 
			if (hasAttribute "const" attr) then true 
			else (hasTypeConstAttr at) 
		| TPtr(pt,attr) -> 
			if (hasAttribute "const" attr) then true 
			else (hasTypeConstAttr pt) 
		| TNamed(ti,attr) -> 
			if (hasAttribute "const" attr) then true 
			else (hasTypeConstAttr ti.ttype)

let rec generatePointer (pt:typ) (tt:typ) (l:lval) (source:file) = 
	let funcName = typeToString "Austin__generate__" pt in
	
	let addressOf = mkAddrOrStartOf l in
	
	let f = emptyFunction funcName in
	f.svar.vtype <- (TFun(pt, Some[("address", voidPtrType, [])], false, [])); 
	
	let vaddress = makeFormalVar f "address" voidPtrType in
	let vproceed = makeLocalVar f "austin_proceed_ptr" intType in
	let vptr = makeLocalVar f "ptr" pt in
	let postAF, postAFP = generatePointerPostAssignment pt in
	
	let argSize = 
		match (unrollType tt) with
			| TVoid _ -> SizeOf(TPtr(TVoid([]), []))
			| TBuiltin_va_list _ -> 
				Log.unimp "Variable argument length lists are not supported\n"
			| _ -> SizeOf(tt) 
	in
	let argProc = mkAddrOf (var vproceed) in
	let argAddr = Lval((var vaddress)) in
	let argFunc = Lval((var postAFP)) in
			
	if (Hashtbl.mem prototypes funcName) then (
		let f' = Hashtbl.find prototypes f.svar.vname in
		Call(Some(l), Lval((var f'.svar)), [addressOf], locUnknown)
	) else (
		Hashtbl.replace prototypes funcName f;
		let s1 = 
			(* assign function pointer to global *)
			mkStmt (Instr([Set((var postAFP), Lval((var postAF.svar)), locUnknown)]))
		in
		let s2 = 
			(* call Austin__GetPtr on vptr *)
			mkStmt (Instr([makeAustinPtrCall (var vptr) argSize argProc argAddr argFunc]))
		in
		let s3 = 
			let ifExp = BinOp(Eq, Lval((var vproceed)), one, intType) in
			let thn = 
				mkBlock [mkStmt (Instr(handleInputType (Mem(Lval(var vptr)), NoOffset) tt source f))]
			in
			let els = mkBlock [] in
			mkStmt (If(ifExp, thn, els, locUnknown))
		in
		let s4 = 
			mkStmt (Return(Some(Lval(var vptr)), locUnknown))
		in
		f.sbody <- mkBlock [s1;s2;s3;s4];
		Hashtbl.replace prototypes funcName f;
		Call(Some(l), Lval((var f.svar)), [addressOf], locUnknown)
	)
and generateArray (t:typ) (base:typ) (d1:exp) (l:lval) (source:file) =  
	let strD1 = 
		match constFold true d1 with
      | Const(CInt64(ni, _, _)) when ni >= Int64.zero -> 
          (string_of_int (i64_to_int ni))
      | e -> "var"
	in
	let prefix = ref ("Austin__generate__Array__"^(strD1)) in
	let rec dimensionsToString (dlist : exp list) (t:typ) = 
		match t with
			| TArray(bt, eo, _) -> 
				let i = lenOfArray eo in
				prefix := (!prefix)^"__"^(string_of_int i);
				dimensionsToString ((integer i)::dlist) bt
			| _ -> ((typeToString ((!prefix)^"__") (unrollType t)), (List.rev dlist))
	in
	let funcName, dlist = dimensionsToString [] base in
	let f = emptyFunction funcName in
	
	let vaddr = makeFormalVar f "address" voidPtrType in
	let addressOf = mkAddrOrStartOf l in
		
	if (Hashtbl.mem prototypes funcName) then (
		let f' = Hashtbl.find prototypes f.svar.vname in
		Call(Some(l), Lval((var f'.svar)), ([addressOf;d1]@dlist), locUnknown)
	) else (
		let tmpArray = makeLocalVar f "tmp" t in
		let austinFunc = emptyFunction "Austin__GetArray" in
		austinFunc.svar.vtype <- TFun(voidPtrType, Some[("size", uintType, []); ("address", voidPtrType, [])], false, []);
		austinFunc.svar.vstorage <- Extern;
		Hashtbl.replace prototypes austinFunc.svar.vname austinFunc;
		Hashtbl.replace prototypes funcName f;
		let s1 = ref dummyStmt in
										
		let counter = ref 0 in
		let rec mkLoops (al:lval) (sizeArgs:exp list) (dims:exp list) = 
			match dims with
				| [] -> (* make austin call Austin__GetArray(size, address) *)
					(
						(*****************)
						let rec mkProduct (twoarg:exp list) (arglist:exp list) = 
							match arglist with
								| [] -> 
									let es = (List.hd twoarg) in
									BinOp(Mult, es, SizeOf(base), (typeOf es))
								| a::rem ->
									(
										match twoarg with
											| [] -> (* add it*)mkProduct [a] rem
											| e::r -> 
												mkProduct [BinOp(Mult, a, e, (typeOf a))] rem
									) 
						in
						let size = mkProduct [] sizeArgs in
						(***********************)
						s1 := mkStmt (Instr([Call(Some((var tmpArray)), Lval((var austinFunc.svar)), [size;Lval((var vaddr))], locUnknown)]));
						
						[mkStmt (Instr(handleInputType al base source f))]
					)
				| d::rem -> 
					(
						let v = makeFormalVar f ("d"^(string_of_int (!counter))) intType in
						let dimVar = makeLocalVar f ("dim__"^v.vname) intType in
						counter := (!counter) + 1;
						let l' = Mem(BinOp(PlusPI, Lval(al), Lval((var dimVar)), (typeOf (Lval(al))))), NoOffset in
						
						let body = mkLoops l' (d::sizeArgs) rem in
						mkForIncr dimVar zero (Lval((var v))) one body
					)
		in
		let stmts = mkLoops (var tmpArray) [] (d1::dlist) in
		f.sbody <- mkBlock ([!s1]@stmts@[mkStmt (Return(Some(Lval(var tmpArray)), locUnknown))]);
		f.svar.vtype <- TFun(t, (Some(List.map(fun v -> (v.vname, v.vtype, []))f.sformals)), false, []);
		Hashtbl.replace prototypes funcName f;
		Call(Some(l), Lval((var f.svar)), ([addressOf;d1]@dlist), locUnknown)
	)
	
and handleInputType (l:lval) (t:typ) (source:file) (containingFdec: fundec) = 
	if (hasTypeConstAttr t) then []
	else( 
	match t with
		| TNamed(ti, _) -> 
			handleInputType l ti.ttype source containingFdec
		| TInt(kind, _) -> [makeIntTypeCall kind l]
		| TFloat(kind, _) -> [makeFloatTypeCall kind l]
		| TPtr(ptype, _) -> 
			if (isFunctionType (unrollType ptype)) then []
			else [generatePointer (removeAllConstAttributes(unrollType t)) (removeAllConstAttributes ptype) l source]
		| TArray(at, lengthO, _) -> 
			(
				(* generate tmp pointer and treat as array - F1*)
				(* for i = 0 to length0 assign the return value of *)
				(* F1 to l[i]*)
				match lengthO with
					| None -> 
						Log.error (Printf.sprintf 
							"Could not get length of array (in TArray) for %s, bailing out\n"
							(Pretty.sprint 255 (Cil.d_lval () l)))
					| Some(len) -> 
						(
							match isInteger (constFold true len) with
								| None -> 
									Log.error (Printf.sprintf 
									"Array length = %s for %s is not an integer (in TArray), bailing out\n"
									(Pretty.sprint 255 (Cil.d_exp () len))
									(Pretty.sprint 255 (Cil.d_lval () l)));
								| Some(ilen) -> 
									let i32len = Int64.to_int ilen in
									let rec mkStmtList pos res = 
										if pos >= i32len then
											res
										else (
											let lv = addOffsetLval (Index((integer pos),NoOffset)) l in
											mkStmtList (pos + 1) (res @ (handleInputType lv (removeAllConstAttributes at) source containingFdec))
										)
									in
									mkStmtList 0 []
						)
			)
		| TComp(compI, _) -> 
			(* l must be base *)
			List.fold_left(
				fun ins field -> 
					let off = Field(field, NoOffset) in
					let lv' = addOffsetLval off l in
					(ins @ (handleInputType lv' (removeAllConstAttributes field.ftype) source containingFdec))
			) [] compI.cfields
		| TEnum(enumI, _) -> [makeIntTypeCall IInt l]
		| _ -> 
			Log.warn (sprintf "Ignoring input %s due to unsupported type %s (%s)\n" (Pretty.sprint 255 (Cil.d_lval () l)) (Pretty.sprint 255 (Cil.d_type () t)) containingFdec.svar.vname);
			[] ) 

let callAustinClearWorkItems () = 
	let clrF = emptyFunction "Austin__ClearWorkItems" in
	setFunctionTypeMakeFormals clrF (TFun(voidType, Some[], false, []));
	Call(None, Lval((var clrF.svar)), [], locUnknown)

class isDefinedVisitor (globVar:varinfo) (res:bool ref) (locals:varinfo list) = object(this)
	inherit nopCilVisitor
		
	method private isLocalVariable () = 
		List.exists(fun v -> (compare v.vname globVar.vname) = 0)locals
		
	method vinst (i:instr) = 
		match i with
			| Set(l,_,_) -> 
				if (Utils.compareLvalByName (var globVar) l) 
					&& not(this#isLocalVariable ())then (
					res := true;
					SkipChildren
				) else
					DoChildren
			| Call(lo, _, _, _) -> 
				(
					match lo with
						| None -> DoChildren
						| Some(l) -> 
							if (Utils.compareLvalByName (var globVar) l) 
								&& not(this#isLocalVariable ()) then (
								res := true;
								SkipChildren
							) else
								DoChildren
				)
			| _ -> DoChildren
end

let isGlobalDefinedInMain (v:varinfo) (source:file) =
	let fo = tryFindFundecFromName source (ConfigFile.find Options.keyRenamedMain) in
	match fo with
		| None -> false
		| Some(f) -> 
			(
				let res = ref false in 
				let vis = new isDefinedVisitor v res f.slocals in
				ignore(visitCilFunction vis f);
				!res
			)
			
let rec isFunctionTypeOrFunctionPointer (t:typ) =
	match (unrollTypeDeep t) with
		| TPtr(pt, _) -> 
			isFunctionTypeOrFunctionPointer pt
		| TFun _ -> true
		| TNamed(ti,_) -> 
			isFunctionTypeOrFunctionPointer ti.ttype
		| _ -> false
	
let rec isUnionType (t:typ) =
		 match (unrollTypeDeep t) with
			| TPtr(pt, _) ->  
				isUnionType pt
			| TNamed(ti,_) -> 
				isUnionType ti.ttype
			| TComp(ci,_) ->  
				not(ci.cstruct)
			| _ -> false

let isDeclaredInput (v:varinfo) = 
	match(tryGetAttribute "austin__input" v.vattr) with
		| None -> false
		| Some _ -> true
										
let getGlobalInputs (source:file) = 
	let checkVarinfo (v:varinfo) = 
		if v.vstorage = Extern then false
		else if (hasVarConstAttr v) then false
		else if (isFunctionTypeOrFunctionPointer v.vtype) then false
		else if (isUnionType v.vtype) then false
		else if (List.mem v.vname !globalsToIgnore) then false
		else (
			not(isGlobalDefinedInMain v source)
		)
	in
	List.filter(fun g -> 
		match g with
			| GVarDecl(v,_) -> checkVarinfo v
			| GVar(v,init,_) -> 
				(
					match init.init with
						| None -> checkVarinfo v
						| Some _ -> false
				)
			| _ -> false
	)source.globals

let explicitArrayConversion (vars:varinfo list) =
	let tryExtractInt (a:attribute) =
		match a with
			| Attr(_, aplist) ->
				try
					let ap = List.find(fun ap' -> match ap' with AInt(i) -> true | _ -> false)aplist in
					match ap with
						| AInt(i) -> i
						| _ -> 0
				with
					| Not_found -> 0   
	in
	let rec isArrayType (t:typ) =
		match t with
			| TPtr(pt,attrs) -> 
				(
					match (Utils.tryGetAttribute "arraylen" attrs) with
						| None -> 
							(
								match (tryGetAttribute "austin__array" attrs) with
									| None -> (false,t,0)
									| Some(a) -> (true,pt,(tryExtractInt a))
							)
						| Some(a) -> (true,pt,(tryExtractInt a))
				)
			| TNamed(tn,attrs) -> 
				(
					match (Utils.tryGetAttribute "arraylen" attrs) with
						| None -> 
							(
								match (tryGetAttribute "austin__array" attrs) with
									| None -> isArrayType tn.ttype
									| Some(a) -> (true,t,(tryExtractInt a))
							)
						| Some(a) -> (true,t,(tryExtractInt a))
				)
			| _ -> (false,t,0) 
	in
	List.map(
		fun v -> 
			let isArray,baseType,len = isArrayType v.vtype in
			if isArray then (
				v.vtype <- TArray(baseType, Some(integer len), []);
			);
			v
	)vars
		
let createTestDriver (fut:fundec) (source : file) = 
	let drv = emptyFunction "Austin__drv" in
	setFunctionTypeMakeFormals drv (TFun(voidType, Some [], false, []));
	
	let globals = 
		List.map(
			fun g -> 
				match g with
					| GVarDecl(v,_) -> v
					| GVar(v, _, _) -> v
					| _ -> 
						Log.error (sprintf "Only accept varinfos but received other global %s\n" (Pretty.sprint 255 (Cil.d_global () g)))
		)(getGlobalInputs source)
	in
	
	let initInstructions = 
		List.fold_left(
			fun ins v -> 
				let v' = 
					if not(v.vglob) then ( 
						makeLocalVar drv v.vname (removeAllConstAttributes v.vtype)
					) else v
				in
				inputVarinfos := v::(!inputVarinfos);
				
				(ins @ (handleInputType (var v') (removeAllConstAttributes v'.vtype) source fut))
		) [] (explicitArrayConversion (globals @ fut.sformals))
	in
	let bodyInstr = 
		Instr((initInstructions @ 
					[callAustinClearWorkItems (); 
					 Call(None, Lval((var fut.svar)), (List.map(fun v -> Lval((var v)))fut.sformals), locUnknown)])) 
	in
	drv.sbody <- mkBlock [(mkStmt bodyInstr)];
	Hashtbl.replace prototypes drv.svar.vname drv;
	drv
	
let addAustinFunctions (source : file) =
	(* add prototypes at the end of globals, but before Austin_drv() *)
	(* add prototypes *)
	Hashtbl.iter(
		fun name fdec -> 
			if (compare name "Austin__drv") = 0 then (
				source.globals <- GVarDecl(fdec.svar, locUnknown)::source.globals	
			) else (
				(* make sure we unroll all the return types of extern functions *)
				if fdec.svar.vstorage = Extern then (
					match fdec.svar.vtype with
						| TFun (ft, args, v, atts) -> 
							let ft' = unrollTypeDeep ft in
							let args' = 
								match args with
									| None -> None
									| Some(a) -> 
										Some(List.map (
											fun (n,at,aatts) -> 
												(n, (unrollTypeDeep at), aatts)
										)a)
						 	in
							fdec.svar.vtype <- TFun(ft', args', v, atts)
						| _ -> ()
				);
				source.globals <- (source.globals @ [GVarDecl(fdec.svar, locUnknown)])
			);
	)prototypes;
	(* add function bodies *)
	Hashtbl.fold(
		fun name fdec nameList -> 
			if(fdec.svar.vstorage <> Extern) then
				source.globals <- (source.globals @ [GFun(fdec, locUnknown)]);
			(name::nameList) 
	) prototypes []
	
	
