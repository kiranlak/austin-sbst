(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open Printf
open Cfginfo
open Utils

open TraceManager

module Log = LogManager

let prototypeFundecs = ref []

let branchInfos : (int,exp) Hashtbl.t = Hashtbl.create Options.hashtblInitSize

let reset () = 
	prototypeFundecs := [];
	Hashtbl.clear branchInfos
	
let addPrototype (f:fundec) = 
	let namesMatch (f':fundec) = (compare f'.svar.vname f.svar.vname) = 0 in
	if not(List.exists namesMatch (!prototypeFundecs)) then
		prototypeFundecs := (f::(!prototypeFundecs));
;;	
let ikindStrAndCast (kind : ikind) = 
	match kind with
		| IChar -> ("Char", TInt(IChar,[]))
		| ISChar -> ("SChar", TInt(ISChar,[]))
		| IUChar -> ("UChar", TInt(IUChar,[]))
		| IBool -> ("Bool", TInt(IBool,[]))
		| IInt -> ("Int", TInt(IInt,[]))
		| IUInt -> ("UInt", TInt(IUInt,[]))
		| IShort -> ("Short", TInt(IShort,[]))
		| IUShort -> ("UShort", TInt(IUShort,[]))
		| ILong -> ("Long", TInt(ILong,[]))
		| IULong -> ("ULong", TInt(IULong,[]))
		| ILongLong -> ("LongLong", TInt(ILongLong,[]))
		| IULongLong -> ("ULongLong", TInt(IULongLong,[]))

let fkindStrAndCast (kind : fkind) = 
	match kind with
		| FFloat -> ("Float", TFloat(FFloat,[]))
		| FDouble -> ("Double", TFloat(FDouble,[]))
		| FLongDouble -> ("LongDouble", TFloat(FLongDouble,[]))	
		
let rec typeToString (t:typ) =
	match (unrollType t) with
		| TVoid _ -> ("Void", voidPtrType)
		| TInt(kind, _) -> ikindStrAndCast kind
		| TFloat(kind, _) -> fkindStrAndCast kind
		| TNamed(ti, _) -> typeToString ti.ttype
		| TPtr(pt, _) -> ("Void", voidPtrType)(*typeToString pt*)
		| TEnum(ei,_) -> ikindStrAndCast ei.ekind
		| _ -> Log.error (Printf.sprintf "invalid distance type: %s\r\n" (Pretty.sprint 255 (Cil.d_type () t)))
		
let getBinOpFuncName (b:binop) (orig:exp) (lhs:exp) (rhs:exp) = 
	match b with
		| Lt -> ("Austin__EvalLessThan__", lhs, rhs)
		| Gt -> ("Austin__EvalGreaterThan__", lhs, rhs)
		| Le -> ("Austin__EvalLessThanEq__", lhs, rhs)
		| Ge -> ("Austin__EvalGreaterThanEq__", lhs, rhs)
		| Eq -> ("Austin__EvalEquals__", lhs, rhs)
		| Ne -> ("Austin__EvalNotEqual__", lhs, rhs)
		| _ ->  ("Austin__EvalNotEqual__", orig, zero)

let getUnOpoFuncName (u:unop) (orig : exp) = 
	match u with
		| Neg -> ("Austin__EvalNotEqual__", orig, zero)
		| BNot -> ("Austin__EvalNotEqual__", orig, zero)
		| LNot -> ("Austin__EvalEquals__", orig, zero)

let invertExpression (e:exp) = 
	let strippedEx, strippedCasts = stripCastsEx e [] in
	match strippedEx with
		| UnOp(u, e', t) ->
			(
				match u with
					| LNot -> reapplyCasts e' strippedCasts
					| _ -> UnOp(LNot, e, t)
			)
		| BinOp(b, lhs, rhs, t) -> 
			(
				match b with
					| Lt -> reapplyCasts (BinOp(Ge, lhs, rhs, t)) strippedCasts
					| Gt -> reapplyCasts (BinOp(Le, lhs, rhs, t)) strippedCasts
					| Le -> reapplyCasts (BinOp(Gt, lhs, rhs, t)) strippedCasts
					| Ge -> reapplyCasts (BinOp(Lt, lhs, rhs, t)) strippedCasts
					| Eq -> reapplyCasts (BinOp(Ne, lhs, rhs, t)) strippedCasts
					| Ne -> reapplyCasts (BinOp(Eq, lhs, rhs, t)) strippedCasts
					| _  -> UnOp(LNot, e, t)
			)
		| _ -> UnOp(LNot, e, (typeOf e))
	
let uint (value : int) = 
	Const(CInt64((Int64.of_int value), IUInt, None))

class branchDistanceVisitor (fut:fundec) = object(this)
	inherit nopCilVisitor 
	
	method private mkSendDistValuesCall (args:exp list) = 
		let f = emptyFunction "Austin__SendBranchDistances" in
		f.svar.vtype <- TFun(voidType, Some[
			("fid", uintType, []);
			("sid", uintType, []);
			("index", uintType, []);
			("values", uintType, [])	
		], true, []);
		addPrototype f;
		Call(None, Lval((var f.svar)), args, locUnknown)

	method private constructIfFunctionCall (distance:varinfo) (sid:int) (index : int) (e:exp) = 
		let (prefix, lhs, rhs), t = 
			match (stripCasts e) with
				| UnOp(u, e', t') -> ((getUnOpoFuncName u e'), (typeOf e'))
				| BinOp(b, lhs', rhs', t') -> 
					((getBinOpFuncName b e lhs' rhs'), (typeOf lhs'))
				| _ -> (("Austin__EvalNotEqual__", e, zero), (typeOf e))
		in
		let name,argType = typeToString t in
		let distFunc = emptyFunction (prefix^name) in
		distFunc.svar.vtype <- 
			TFun(TFloat(FLongDouble,[]), Some[("lhs", argType, []); ("rhs", argType, [])], false, []); 
		addPrototype distFunc;
		let i1 = Call(Some((var distance)), Lval((var distFunc.svar)), [mkCast lhs argType;mkCast rhs argType], locUnknown) in
		let i2 = this#mkSendDistValuesCall 
						[
							(uint fut.svar.vid); 
							(uint sid);
							(uint index);
							(uint 1); (* number of values *)
							(Lval((var distance)))
						] in
		[i1;i2]
		
	method private instrumentIfStatement (sid:int) (e:exp) (thn:block) (els:block) = 
		(* invert expression, because we want to know how far away execution was from avoiding this branch*)
		if sid = (-1) then 
			Log.error (Printf.sprintf "sid = -1 for e=%s\n" (Pretty.sprint 255 (Cil.d_exp()e)));
			
		let distance = makeLocalVar fut 
			("__AUSTIN__distance__"^(string_of_int fut.svar.vid)^"__"^(string_of_int sid)) (TFloat(FLongDouble,[])) in
			
		let inverseExp = invertExpression e in
		addInstrsToBlock thn (this#constructIfFunctionCall distance sid 0 inverseExp);
		addInstrsToBlock els (this#constructIfFunctionCall distance sid 1 e)
			
	method private callAustinMin (args:exp list) = 
		let f = emptyFunction "Austin__Min" in
		f.svar.vtype <- TFun(TFloat(FLongDouble,[]), Some["arg1", (TFloat(FLongDouble,[])), [];"arg2", (TFloat(FLongDouble,[])),[]], false, []);
		let v = makeTempVar fut (TFloat(FLongDouble,[])) in
		addPrototype f;
		(v, (Call(Some((var v)), Lval((var f.svar)), args, locUnknown)))
				
	method private instrumentSwitchStatement (currentStmt:stmt) (sid:int) (e:exp) (cases:stmt list) = 
		
		if sid = (-1) then 
			Log.error (Printf.sprintf "sid = -1 for e=%s\n" (Pretty.sprint 255 (Cil.d_exp()e)));
		
		let caseswodef = removeDefaultCase cases in
		
		let name,argType = typeToString (unrollTypeDeep(typeOf e)) in
		let distFunc = emptyFunction ("Austin__EvalEquals__"^name) in
		
		distFunc.svar.vtype <- TFun(TFloat(FLongDouble,[]), Some[("lhs", argType, []); ("rhs", argType, [])], false, []);
		
		addPrototype distFunc;
		
		let makeDistanceVar (name : string) = 
			makeLocalVar fut name (TFloat(FLongDouble,[])) 
		in
		
		let htCases : (int, (bool * varinfo list)) Hashtbl.t = Hashtbl.create (List.length caseswodef) in
		let counter = ref 0 in
		let caseDistances = 
			List.fold_left (
				fun ilist s -> 
					let caseExpressions = getSwitchCaseExpressions s in
					assert((List.length caseExpressions) > 0);
					let distanceVars = List.map(
						fun case -> 
							let v = makeDistanceVar 
								("__AUSTIN__distance__"^(string_of_int fut.svar.vid)^"__"^(string_of_int sid)^"__"^(string_of_int (!counter)))
							in
							incr counter;
							v
						) caseExpressions
					in

					Hashtbl.add htCases s.sid (false, distanceVars);
					
					let dcalls = 
						List.map2(
							fun v case -> 
								Call(Some((var v)), Lval((var distFunc.svar)), [mkCast e argType;mkCast case argType], locUnknown)	
						)distanceVars caseExpressions
					in
					(dcalls @ ilist)
			) [] caseswodef
		in
		let computeDefaultDistance = []
		(**TODO: default distance should be negation for each case, and then minimum of all the other cases vs default case *)
			(*match(tryGetDefaultCase cases)with
				| None -> []
				| Some(s) -> 
					(
						let defVar = makeDistanceVar 
							("__AUSTIN__distance__"^(string_of_int fut.svar.vid)^"__"^(string_of_int sid)^"__def")
						in
						(* iter through hashtable and find minimum *)
						let arglist = Hashtbl.fold(
							fun id (_,vars) elist -> 
								((List.map(fun v -> Lval((var v)))vars)@elist)
						) htCases [] in

						Hashtbl.add htCases s.sid (true, [defVar]);
						
						if (List.length arglist) = 1 then (
							[Set((var defVar), (List.hd arglist), locUnknown)]
						) else (
							let rec stackCalls (ilist) (twoarg:exp list) (arglist:exp list) = 
								match arglist with
									| [] -> (ilist, (List.hd twoarg))
									| a::rem ->
										(
											match twoarg with
												| [] -> (* add it*)stackCalls ilist [a] rem
												| e::r -> 
													let v, i = this#callAustinMin [e;a] in
													stackCalls (i::ilist) [Lval((var v))] rem
										) 
							in
							let ilist,finalResult = stackCalls [] [] arglist in
							(List.rev (Set((var defVar), finalResult, locUnknown)::ilist))
						)
					)*)
		in
		(* insert send distance calls *)
		counter := 0;
		List.iter(
			fun s -> 
				let args = ref [] in
				Hashtbl.iter(
					fun id (_,vars) -> 
						if id <> s.sid then (
							args := ((List.map(fun v -> Lval((var v)))vars) @ (!args))
						)
				)htCases;
				let i = 
					let l1 = [
						uint fut.svar.vid;
						uint sid; 
						uint (!counter);
						uint (List.length (!args)); ] in
				  let distargs = (l1 @ (!args)) in
					this#mkSendDistValuesCall distargs
				in
				incr counter;
				pushInstrBeforeStmt s [i]
		) cases;
		pushInstrBeforeStmt currentStmt (caseDistances@computeDefaultDistance)
		
	method vstmt (s:stmt) = 
		match s.skind with
			| If(e, thn, els, loc) ->
				let e' = propagateNegation e in
				
				(* use the original condition (e) rather than the one with negations removed (e.g. e') *)
				Hashtbl.replace branchInfos s.sid e;
				
				this#instrumentIfStatement s.sid e' thn els;
				DoChildren
			| Switch(e, _,cases,_) -> 
				(**START LOGGING**)
				let printE =
					let rec searchLabels (labelExpr:exp list) (labels : label list) =
						match labels with
							| [] -> labelExpr
							| l::rem -> 
								(
									match l with
										| Case(e', _) -> searchLabels (e'::labelExpr) rem
										| Default _ -> searchLabels ((mkString "default")::labelExpr) rem
										| _ -> searchLabels labelExpr rem
								) 
					in
					let res = List.fold_left(
						fun e' s' -> 
								let l = List.fold_left(
									fun bexp lexp ->
										if (List.length bexp) = 0 then
											[lexp]
										else (
											[BinOp(LOr, (List.hd bexp), lexp, intType)]
										)	
								)[] (List.rev (searchLabels [] s'.labels)) in
								if (List.length l) = 0 then
									e'
								else (
									if (List.length e') = 0 then
										[BinOp(Eq, e, (List.hd l), intType)]
									else (
										let b1 = BinOp(Eq, e, (List.hd l), intType) in
										[BinOp(LOr, (List.hd e'), b1, intType)]
									) 
								)
					) [] cases in
					if (List.length res) = 0 then e else (List.hd res) 
				in
				Hashtbl.replace branchInfos s.sid printE;
				(**END LOGGING**)
				this#instrumentSwitchStatement s s.sid e cases;
				DoChildren 
			| _ -> DoChildren
				
end
let saveBranchIDInfo () = 
	let outchan = open_out (ConfigFile.find Options.keyBranchIds) in
  Hashtbl.iter(
		fun id e -> 
			let str = 
				(string_of_int id)^":"^(Pretty.sprint 255 (Cil.d_exp () e))^"\r\n" 
			in
			output_string outchan str
	)branchInfos;
  close_out outchan

let main (source : file) (fut : fundec) (ignoreList:string list) = 
		
	computeControlDependencies source fut;
	
	assert((List.length fut.sallstmts) > 0);
	
	let vis = new branchDistanceVisitor fut in
	
	ignore(visitCilFunction vis fut);
		
	saveControlDependencies (ConfigFile.find Options.keyCfgInfo);
	
	saveBranchIDInfo ();
	
	(!prototypeFundecs,[])