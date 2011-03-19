(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open Printf
open Symbolic
open Options
open Solution
open MainLib
open Utils

module Log = LogManager

external findAddressInformation : int -> int -> (string*int*string*float*int64) = "findAddressInformation"

let lvalAlia : (lval list) LvalHashtbl.t = LvalHashtbl.create Options.hashtblInitSize

let currentTracePos = ref 0

let symTraceInitialize () = 
	source := (Utils.unmarshalSource (ConfigFile.find Options.keyBinInstrumentedSrouce));
	Symbolic.loadStateFromFile ()

let rec findTransitiveLvalAlia (l:lval) (res:lval list) = 
	(* find all alia for l. foreach alia find its alia *)
	if not(LvalHashtbl.mem lvalAlia l) then (
		res
	) else (
		let alia = LvalHashtbl.find lvalAlia l in
		List.fold_left(
			fun res' l' -> 
				if (Utils.compareLval l' l) then (
					res'
				) else (
					let alia' = findTransitiveLvalAlia l' [] in
					(* filter all lvalues that are already in res' *)
					let falia' = List.filter(fun l'' -> not(List.exists(fun l''' -> Utils.compareLval l'' l''')res'))alia' in
					List.rev_append falia' res'
				)
		)alia alia	
	)

let findTransitiveExpAlia (e:exp) = 
	match (stripCasts e) with
		| Lval(l) ->
			findTransitiveLvalAlia l [] 
		| _ -> []
	
let findSolutionLvalFromAddress (isDeref:bool) (address:int64) (targetAddr:int64) (offset:int) = 
	let matches = List.filter(
			fun n -> 
				match n.concreteVal with 
					| None -> false
					| Some(conc) -> 
						(address = conc.address && offset = conc.offset) || (isDeref && (conc.address = targetAddr))
		)!inputNodes
	in
	List.map(fun n -> n.cilLval)matches
	
let findAliaFromTracePos (isDeref:bool) (index:int) = 
	let strAddress,offset,strTargetAddr,fvalue,ivalue = findAddressInformation !currentTracePos index in
	let address = Int64.of_string strAddress in
	let targetAddress = Int64.of_string strTargetAddr in
	let lvals = findSolutionLvalFromAddress isDeref address targetAddress offset in
	((List.fold_left(
		fun res l -> 
			List.rev_append (findTransitiveLvalAlia l []) res
	)lvals lvals), fvalue, ivalue)
	
let filterExpFromAlia (e:exp) (alia:exp list) =
	let norm_e = normalizeArrayAccessEx (stripCasts e) in
	List.filter(
		fun e' -> 
			not(Utils.compareExp norm_e  (normalizeArrayAccessEx (stripCasts e')))
	)alia
	  	
let filterLvalFromAlia (l:lval) (alia:lval list) = 
	let norm_l = normalizeArrayAccess l in
	List.filter(
		fun l' -> not(Utils.compareLval norm_l (normalizeArrayAccess l'))
	)alia
	 
let handleAssignmentStatement (l:lval) (e:exp) = 
	let e' = rewriteExpression e in
	let existing = 
		try
			LvalHashtbl.find lvalAlia l 
		with
			| Not_found -> []
	in
	let inputAlia = 
		let alia,_,_ = findAliaFromTracePos (Utils.isPointerDeref l) (-1) in
		filterLvalFromAlia l (alia@existing)
	in
	List.iter(
		fun lv -> assign l e'
	)(l::inputAlia)
	
let getExprAliaListAndConcreteExp (e:exp) (index:int) = 
	let lvalExpAlia,e_fval,e_ival = findAliaFromTracePos (Utils.isPointerDerefEx e) index in
	let expConcr = 
		let t = unrollType (typeOf e) in
			if isPointerType t || isIntegralType t then (
				match t with
					| TInt(kind,_) -> Const(CInt64(e_ival, kind, None))
					| _ -> Const(CInt64(e_ival, (intKindForValue e_ival true), None))
			) else (
				Const(CReal(e_fval, FLongDouble, None))
			)
	in
	let e' = rewriteExpression e in
	let expAlia = filterExpFromAlia e' (List.map(fun lv -> Lval(lv))lvalExpAlia) in		
	if not(isExpUndefined e') then (
		((e'::expAlia), expConcr)
	) else (
		(expAlia, expConcr)
	)
	
let handleBranchingStmt (e:exp) (ifStmt:bool) (index:int) = 
	match (stripCasts e) with
		| BinOp(b, e1, e2, t) when (Utils.isComparisonOp b) -> 
			let b' = if not(ifStmt) || index = 0 then b else (Utils.invertRelBinaryOp b) in
			let e1List,e1Concrete = getExprAliaListAndConcreteExp e1 0	in
			let e2List,e2Concrete = getExprAliaListAndConcreteExp e2 1	in
			let lene1 = List.length e1List in
			let lene2 = List.length e2List in
			if lene1 = 0 && lene2 = 0 then (
				(false, [])
			)	else if lene1 = 0 then (
				(true, (
					List.map (
						fun e'' -> BinOp(b', e1Concrete, e'', t)
					) e2List)) 
			) else if lene2 = 0 then (
				(true, (
					List.map (
						fun e'' -> BinOp(b', e'', e2Concrete, t)
					) e1List))
			) else if lene1 > 0 && lene2 > 0 then (
				let _e1 = List.hd e1List in
				let _e2 = List.hd e2List in
				let _e1rest = List.map(fun _ex -> BinOp(Eq, _ex, _e1, (typeOf _e1)))(List.tl e1List) in
				let _e2rest = List.map(fun _ex -> BinOp(Eq, _ex, _e2, (typeOf _e2)))(List.tl e2List) in
				(true, ((BinOp(b', _e1, _e2, t))::(_e1rest@_e2rest)))
			) else (
				(false, [])
			)
		| UnOp(u, e1, t) -> 
			let e1List,e1Concrete = getExprAliaListAndConcreteExp e1 0 in
			if (List.length e1List) > 0 then (
				let e1'' = List.map (
					fun e'' -> 
						if index = 0 then
							UnOp(u, e'', t)
						else
							Utils.tryInvertOp (UnOp(u, e'', t))
				) e1List 
				in
				(true, e1'')
			) else
				(false, [])
		| _ -> 
			let elist,eConcrete = getExprAliaListAndConcreteExp e 0 in
			if (List.length elist) > 0 then (
				let b' = if index = 0 then Ne else Eq in
				let t = typeOf e in
				(true, (
					List.map (
						fun e'' -> BinOp(b', e'', Cil.zero, t)
					) elist))
			) else
				(false, [])
	
let findStmt (sid:int) = 
	let rec searchStmts (stmts:stmt list) =
		match stmts with
			| [] -> None
			| [s] -> 
				if s.sid = sid then Some(s) else None
			| s::rem -> 
				if s.sid = sid then Some(s) else searchStmts rem 
	in
	let handleGlobal (g:global) =
		match g with
			| GFun(f, _) when not(startsWith "Austin__" f.svar.vname) && not((compare "main" f.svar.vname) = 0) -> 
				if (List.length f.sallstmts = 0) && 
					(List.length f.sbody.bstmts > 0) then
						Log.error (sprintf "Function %s has no (missing) CFG info\n" f.svar.vname);
				(Some(f), (searchStmts f.sallstmts))
			| _ -> (None, None) 
	in
	let rec searchGlobals (globs:global list) = 
		match globs with
			| [] -> None,None
			| [g] -> handleGlobal g
			| g::rem -> 
				let fo,res = handleGlobal g in
				(
					match res with
						| None -> searchGlobals rem
						| _ -> fo,res
				)
	in
	match (searchGlobals !source.globals) with
		| _, None -> Log.error (sprintf "Failed to find stmt %d\n" sid)
		| None, Some(s) -> Log.error (sprintf "Found stmt %d but failed to find containing function\n" sid)
		| Some(f), Some(s) -> f,s 
								
let executeStmt (sid:int) (index:int) = 
	let fdec, s = findStmt sid in
	match s.skind with
		| Goto _ | Block _ | TryFinally _ | TryExcept _ -> ()
		| Instr(ilist) -> 
			assert((List.length ilist) < 2);
			List.iter(
				fun i -> 
					(*Log.log (Printf.sprintf "doing instr=%s (%d)\n"
						(Pretty.sprint 255 (Cil.d_instr()i)) sid);*)
					match i with
						| Set(l,e,_) -> 
							handleAssignmentStatement l e
						| Call(lo,fexp,args,_) -> 
							(* rewrite args, and push lo on function stack*)
							let f = Utils.tryFindFundec fexp !source in
							(
								match f with
									| Some(f') when not(endsWith "__mock" f'.svar.vname) -> 
										(
											(**TODO: handle vararg functions. For now use assertion to stop when we have a vararg*)
											if (List.length f'.sformals) <> (List.length args) then (
												Log.error (Printf.sprintf "%s seems to be a vararg function (%d formals, but %d args)\n"
													f'.svar.vname
													(List.length f'.sformals)
													(List.length args));
											);
											call lo f' args
										)
									| _ -> 
										(
											List.iter(fun arg -> 
												let t = typeOf arg in
												if (isPointerType t) || (isFunctionType t) || 
													 (isArrayType t) then (
													makeExpUndefined arg !state
												)
											)args;
											match lo with 
												| None -> (* no return value *) ()
												| Some(l) -> unassign l !state
										)
							)
						| _ -> ()
			) ilist
		| Return(eo, _) -> return eo 
		| Break _ -> (* nothing to do *) ()
		| Continue _  -> (* nothing to do *) ()
		| If(e, thn, el, _) -> (* update path condition*)
			assert(index <> (-1)); 
			(
				match (handleBranchingStmt e true index) with
					| (true, e') -> 
						updatePathCondition (s.sid,index,[e']) 
					| _ -> ()
			)
		| Switch(e, bd, cases, _) -> (* update path condition*)
			assert(index <> (-1) && ((List.length cases) > index)); 
			let case = List.nth cases index in
			let labels = Utils.getSwitchCaseExpressions case in
			let elist = List.fold_left(
				fun expl label -> 
					let condition = BinOp(Eq, e, label, (typeOf e)) in
					let ncondition = BinOp(Ne, e, label, (typeOf e)) in
					match (handleBranchingStmt condition false index) with
						| (false, _) -> ([ncondition]::expl)
						| (true, condition') -> (condition'::expl)
				) [] labels
			in
			if (List.length elist) > 0 then
				updatePathCondition (s.sid,index,elist);
		| Loop _ -> (* nothing to do because it's a while(1) loop*) ()

let executeSymTrace (stmtInfo:(int * int) list) = 
	(*Log.log (Printf.sprintf "received %d statements\n" (List.length stmtInfo));*)
	symTraceInitialize();
	List.iter(
		fun (sid,index) -> 
			executeStmt sid index;
			incr currentTracePos
	)(List.rev stmtInfo);
	savePathConditiontoFile ()
;;
Callback.register "executeSymTrace" executeSymTrace;;