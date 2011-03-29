(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open Rmtmps

module Log = LogManager

let addExplicitReturnStmt = ref false

let convertInstrToStmt (source : file) = 
	Ciltools.one_instruction_per_statement source

let mockFunctions : (string,(varinfo*fundec)) Hashtbl.t = Hashtbl.create 100

let reset() = 
	Hashtbl.clear mockFunctions
	
let mkMockFunction (v:varinfo) = 
	let rec generateMockReturnVal (t:typ) = 
		match t with
			| TVoid _ -> None
			| TInt(ikind,_) -> 
				Some(Const(CInt64(Int64.zero, ikind, None)))
			| TFloat(fkind,_) -> 
				Some(Const(CReal(0.0, fkind, None)))
			| TPtr _ ->  
				Some(mkCast Cil.zero t)
			| TArray _ | TFun _ | TComp _ | TBuiltin_va_list _ -> 
				Log.unimp "Cannot generate mock functions for TArray, TFun, TComp, TBuiltin_va_list\n"
			| TNamed(ti, _) -> generateMockReturnVal ti.ttype
			| TEnum(ei,_) -> 
				Some(Const(CInt64(Int64.zero, ei.ekind, None))) 
	in
	match (unrollType v.vtype) with
		| TFun(rt, args, isvararg, attrs) -> 
			let m = emptyFunction (v.vname^"__mock") in
			m.svar.vtype <- TFun(rt,args,isvararg,attrs);
			(
				match args with
					| None -> m.sformals <- []
					| Some(_args) -> 
						m.sformals <- List.map(fun (name,t',_) -> makeFormalVar m name t')_args
			);
			(
				let s = mkStmt (Return((generateMockReturnVal rt), locUnknown)) in
				m.sbody <- (mkBlock [s]);
			);
			Hashtbl.replace mockFunctions m.svar.vname (v,m);
			m.svar
		| _ -> v
		
class removeUnsafeFileIOVisitor = object(this)
	inherit nopCilVisitor
	
	val forbiddenCalls = [
		"remove";
		"rename";
		"fclose";
		"fflush";
		"setbuf";
		"setvbuf";
		"fprintf";
		"vfprintf";
		"fputc";
		"fputs";
		"_IO_putc";
		"_IO_puts";
		"fwrite";
		"fgetpos";
		"fseek";
		"fsetpos";
		"ftell";
		"rewind";
		"clearerr";
		"feof";
		"ferror";
	]
	
	val returnMockValue = [
		"tmpfile";
		"tmpnam";
		"fopen";
		"freopen";
		"fscanf";
		"scanf";
		"fgetc";
		"fgets";
		"getc";
		"_IO_getc";
		"getchar";
		"gets";
		"ungetc";
		"fread";
	]

	method private doChange (v:varinfo) = 
		if (List.exists(fun n -> (compare n v.vname) = 0)forbiddenCalls) then (
			let v' = mkMockFunction v in
			Some(v')
		) else if(List.exists(fun n -> (compare n v.vname) = 0)returnMockValue) then (
			let v' = mkMockFunction v in
			Some(v')
		) else
			None
				
	method vfunc (f:fundec) = 
		let vopt = this#doChange f.svar in
		(
			match vopt with
				| Some(v') -> f.svar <- v'
				| None -> ()
		);
		DoChildren
		
	method vvrbl (v:varinfo) = 
		if isFunctionType v.vtype then (
			match (this#doChange v) with
				| None -> SkipChildren
				| Some(v') -> ChangeTo v'
		) else SkipChildren
end
class insertMockFunctionVisitor = object(this)
	inherit nopCilVisitor
	
	method vglob (g:global) = 
		match g with
			| GVarDecl(v, loc) -> 
				(
					if (Hashtbl.mem mockFunctions v.vname) then (
						let old,newF = Hashtbl.find mockFunctions v.vname in
						Hashtbl.remove mockFunctions v.vname;
						let g' = [GVarDecl(newF.svar, loc);GFun(newF,locUnknown)] in
						ChangeTo g'
					) else 
						DoChildren
				)
			| GFun(f, loc) -> 
				(
					if (Hashtbl.mem mockFunctions f.svar.vname) then (
						let old,newF = Hashtbl.find mockFunctions f.svar.vname in
						Hashtbl.remove mockFunctions f.svar.vname;
						let g' = [GVarDecl(newF.svar, locUnknown);GFun(newF,loc)] in
						ChangeTo g'
					) else 
						DoChildren
				)
			| _ -> DoChildren
end
class removeFunctionsVisitor (source:file) = object(this)
	inherit nopCilVisitor
	
	val faustCatchError = 
		let f = emptyFunction "Austin__catch_errors" in
		f.svar.vtype <- TFun(voidType, Some["sig", intType, []], false, []);
		f
		
	method private mkCall name typ lo args loc = 
		(*let f = emptyFunction name in
		f.svar.vtype <- typ;*)
		let fvar = findOrCreateFunc source name typ in
		Call(lo, Lval(var fvar), args, loc)
		
	method vinst (i:instr) =  
		match i with
			| Call(lo, f, args, loc) -> 
				(
					match f with
						| Lval(fv) -> 
							(
								match fv with
									| Var v,_ -> 
										(
											if (compare v.vname "malloc") = 0 then (
												let i' = this#mkCall "Austin__Malloc" (typeOf f) lo args loc in
												ChangeTo [i']
											)else if (compare v.vname "realloc") = 0 then (
												let i' = this#mkCall "Austin__Realloc" (typeOf f) lo args loc in
												ChangeTo [i']
											)else if (compare v.vname "free") = 0 then (
												let i' = this#mkCall "Austin__Free" (typeOf f) lo args loc in
												ChangeTo [i']
											) else if (compare v.vname "exit") = 0 then (
												let i' = Call(None, Lval(var faustCatchError.svar), args, loc) in
												ChangeTo [i']
											) else if (compare v.vname "abort") = 0 then (
												let i' = Call(None, Lval(var faustCatchError.svar), [integer 6], loc) in
												ChangeTo [i']
											) else
												DoChildren
										)
									| _ -> DoChildren
							)
						| _ -> DoChildren
				)
			| _ -> DoChildren
end
let removeForbiddenFunctionCalls (source:file) = 
	let vis = new removeFunctionsVisitor source in
	visitCilFileSameGlobals vis source
	
let removeUnsafeCode (source:file) = 
	removeForbiddenFunctionCalls source;
	let vis = new removeUnsafeFileIOVisitor in
	visitCilFileSameGlobals vis source;
	let vis2 = new insertMockFunctionVisitor in
	visitCilFile vis2 source;
	let defs = 
		Hashtbl.fold(
			fun name (old,newF) mdefs -> 
				(GFun(newF,locUnknown))::mdefs
		) mockFunctions [] 
	in
	let rec addRestBeforeFirstFunc pre rem res = 
		match rem with
			| [] -> ((List.rev pre) @ defs)
			| g::rem -> 
				(
					match g with
						| GFun _ -> ((List.rev pre) @ defs @ (g::rem))
						| _ -> addRestBeforeFirstFunc (g::pre) rem res 
				)
	in
	source.globals <- (addRestBeforeFirstFunc [] source.globals [])
	
class visRemoveRegister = object
	inherit nopCilVisitor
	method vvdec (v:varinfo) = 
		match v.vstorage with
			| Register ->
				v.vstorage <- NoStorage;
				SkipChildren
			| _ -> SkipChildren
end
let removeRegisterStorage (source : file) = 
	let vis = new visRemoveRegister in
	visitCilFile vis source
	
let renameMain (globals : global list) = 
	let rec searchGlobals (glbs : global list) = 
		match glbs with
			| [] -> ()
			| g::rem -> 
				(
					match g with
						| GFun(f, _) when f.svar.vname = "main" -> 
							f.svar.vname <- (ConfigFile.find Options.keyRenamedMain)
						| _ -> searchGlobals rem
				)
	in
	searchGlobals globals
	
class returnStmtVisitor (missingReturns:fundec list ref) = object
	inherit nopCilVisitor
	
	val mutable currentFunc = dummyFunDec
	val mutable hasReturn = false
	
	method vfunc (f:fundec) = 
		match f.svar.vtype with
			| TFun(TVoid _, _, _, _) -> 
				hasReturn <- false;
				ChangeDoChildrenPost(f,
					fun f' -> 
						if not(hasReturn) then 
							missingReturns := (currentFunc::(!missingReturns));
						f'
				)
			| _ -> SkipChildren
	
	method vstmt (s:stmt) =
		if currentFunc = dummyFunDec || (startsWith "Austin__" currentFunc.svar.vname) then SkipChildren
		else (
			match s.skind with
				| Return _ -> hasReturn <- true; SkipChildren
				| _ -> DoChildren 
		)
end
let insertExplicitReturnStatement (source:file) = 
	if !addExplicitReturnStmt then (
		let missing = ref [] in
		let vis = new returnStmtVisitor missing in
		visitCilFileSameGlobals vis source;
		let rkind = Return(None, locUnknown) in
		List.iter(
			fun f -> 
				let s = mkStmt rkind in
				let new_body = 
					match f.sbody.bstmts with
						| [] -> (* empty function??*) [s]
						| _ -> f.sbody.bstmts @ [s]
				in
				f.sbody.bstmts <- new_body
		)!missing
	)
	