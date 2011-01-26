(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open Printf
open Symbolic
open Options
open Solution
open Utils
open MainLib

module Log = LogManager

external findAddressInformation : int -> int -> (string*int*string*float*int64) = "findAddressInformation"

let lvalAlia : (lval list) LvalByNameHashtbl.t = LvalByNameHashtbl.create Options.hashtblInitSize

let currentTracePos = ref 0

let symTraceInitialize () = 
	source := (unmarshalSource (ConfigFile.find Options.keyBinInstrumentedSrouce));
	Symbolic.loadStateFromFile (ConfigFile.find Options.keySymState)

class isSymbolicExprVisitor (isInputSymbol:bool ref) = object(this)
	inherit nopCilVisitor
	
	method private isInputSymbol (l:lval) = 
		match (tryFindLvalInStackFrames l) with
			| Some(symLv) -> 
				(
					if symLv.isInput then (
						true
					) else (
						false
					)
				)
			| None -> false

	method vlval (l:lval) = 
		if not(this#isInputSymbol l) then (
			isInputSymbol := false;
			SkipChildren
		) else (
			DoChildren
		)
		
	method voffs (o:offset) = 
		SkipChildren
				
	method vexpr (e:exp) = 
		if isConstant e then (
			isInputSymbol := false;
			SkipChildren
		) else 
			DoChildren
end
let isPureSymbolicExpression (e:exp) = 
	let inputsOnly = ref true in
	let vis = new isSymbolicExprVisitor inputsOnly in
	ignore(visitCilExpr vis e);
	!inputsOnly

let rec findTransitiveLvalAlia (l:lval) (res:lval list) = 
	if not(LvalByNameHashtbl.mem lvalAlia l) then (
		res
	) else (
		let alia = LvalByNameHashtbl.find lvalAlia l in
		List.fold_left(
			fun res' l' -> 
				if (compareLvalByName l' l) then (
					res'
				) else 
					List.rev_append (findTransitiveLvalAlia l' []) res'
		)alia alia	
	)

let findTransitiveExpAlia (e:exp) = 
	match (stripCasts e) with
		| AddrOf(l) | StartOf(l) | Lval(l) ->
			findTransitiveLvalAlia l [] 
		| _ -> []
	
let updateAliaList (l:lval) (e:exp) (existing:lval list) = 
	match (stripCasts e) with
		| AddrOf(l') -> 
			let l'' = rewriteLval l' in
			let toAdd = 
				let toAdd' = (existing @ (List.filter(fun lv1 -> not(List.mem lv1 existing))(findTransitiveLvalAlia l'' []))) in
				if not(List.mem l'' toAdd') then
					(l''::toAdd')
				else
					toAdd'
			in
			LvalByNameHashtbl.replace lvalAlia l toAdd;
			toAdd	
		| StartOf(l') | Lval(l') -> 
			let l'' = rewriteLval l' in
			if (isPointerType (typeOfLval l'')) && not(isPointerDeref l'') then (
				let toAdd = 
					let toAdd' = (existing @ (List.filter(fun lv1 -> not(List.mem lv1 existing))(findTransitiveLvalAlia l'' []))) in
					if not(List.mem l'' toAdd') then
						(l''::toAdd')
					else
						toAdd'
				in
				LvalByNameHashtbl.replace lvalAlia l toAdd;
				toAdd
			) else
				existing
		| _ -> existing
	
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
		
let handleAssignmentStatement (l:lval) (e:exp) (fo:fundec option) = 
	let e' = rewriteExpr e in
	let existing = 
		try
			LvalByNameHashtbl.find lvalAlia l 
		with
			| Not_found -> []
	in
	if not(isPureSymbolicExpression e') then (
		(* check if address matches any of the inputs *)
		let inputAlia,_,_ = findAliaFromTracePos (isPointerDeref l) (-1) in
		updateState (l::(updateAliaList l e' (existing@inputAlia))) fo (SymEx(CilExpr(e')))
	)	else (
		updateState (l::(updateAliaList l e' existing)) fo (SymEx(CilExpr(e')))
	)
	
let getExprAliaListAndConcreteExp (e:exp) (index:int) = 
	let lvalExpAlia,e_fval,e_ival = findAliaFromTracePos (isPointerDerefEx e) index in
	let expAlia = List.filter(fun e' -> not(compareExp (stripCasts e') (stripCasts e)))(List.map(fun lv -> Lval(lv))lvalExpAlia) in
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
	let e' = rewriteExpr e in		
	if (isPureSymbolicExpression e') then (
		((e'::expAlia), expConcr)
	) else (
		(expAlia, expConcr)
	)

let isRelationalOp (b:binop) = 
	match b with
		| Lt | Gt | Le | Ge | Eq | Ne -> true
		| _ -> false
		
let handleBranchingStmt (e:exp) (ifStmt:bool) (index:int) = 
	match (stripCasts e) with
		| BinOp(b, e1, e2, t) when (isRelationalOp b) -> 
			let b' = if not(ifStmt) || index = 0 then b else (invertRelBinaryOp b) in
			let e1List,e1Concrete = getExprAliaListAndConcreteExp e1 0	in
			let e2List,e2Concrete = getExprAliaListAndConcreteExp e2 1	in
			let lene1 = List.length e1List in
			let lene2 = List.length e2List in
			if lene1 = 0 && lene2 = 0 then (
				(false, Cil.zero)
			)	else if lene1 = 0 then (
				(true, (List.fold_left (
				fun res e'' -> 
					if res = Cil.zero then BinOp(b', e1Concrete, e'', t)
					else BinOp(LAnd, (BinOp(b', e1Concrete, e'', t)), res, t)
				) Cil.zero e2List)) 
			) else if lene2 = 0 then (
				(true, (List.fold_left (
				fun res e'' -> 
					if res = Cil.zero then BinOp(b', e'', e2Concrete, t)
					else BinOp(LAnd, (BinOp(b', e'', e2Concrete, t)), res, t)
				) Cil.zero e1List))
			) else if lene1 > 0 && lene2 > 0 then (
				let _e1 = List.hd e1List in
				let _e2 = List.hd e2List in
				let _e1rest = List.map(fun _ex -> BinOp(Eq, _ex, _e1, (typeOf _e1)))(List.tl e1List) in
				let _e2rest = List.map(fun _ex -> BinOp(Eq, _ex, _e2, (typeOf _e2)))(List.tl e2List) in
				(true, (List.fold_left(fun res item -> BinOp(LAnd, res, item, t))(BinOp(b', _e1, _e2, t)) (_e1rest @ _e2rest)))
			) else (
				(false, Cil.zero)
			)
		| UnOp(u, e1, t) -> 
			let e1List,e1Concrete = getExprAliaListAndConcreteExp e1 0 in
			if (List.length e1List) > 0 then (
				let e1'' = List.fold_left (
					fun res e'' -> 
						let ue' = 
							if index = 0 then
								UnOp(u, e'', t)
							else
								tryInvertOp (UnOp(u, e'', t))
						in
						if res = Cil.zero then (
							 ue'
						)	else (
							BinOp(LAnd, ue', res, t)
						)
				) Cil.zero e1List 
				in
				(true, e1'')
			) else
				(false, Cil.zero)
		| _ -> 
			let elist,eConcrete = getExprAliaListAndConcreteExp e 0 in
			if (List.length elist) > 0 then (
				let b' = if index = 0 then Ne else Eq in
				let t = typeOf e in
				(true, (List.fold_left (
					fun res e'' -> 
						if res = Cil.zero then BinOp(b', e'', Cil.zero, t)
						else BinOp(LAnd, (BinOp(b', e'', Cil.zero, t)), res, t)
				) Cil.zero elist))
			) else
				(false, Cil.zero)
	
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
			vassert((List.length ilist) < 2) "less than 2 instructions\n";
			List.iter(
				fun i -> 
					(*Log.log (Printf.sprintf "doing instr=%s (%d)\n"
						(Pretty.sprint 255 (Cil.d_instr()i)) sid);*)
					match i with
						| Set(l,e,_) -> 
							if (isGlobalVar l) then
								handleAssignmentStatement l e None
							else
								handleAssignmentStatement l e (Some(fdec))
						| Call(lo,fexp,args,_) -> 
							(* rewrite args, and push lo on function stack*)
							let f = tryFindFundec fexp !source in
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
											symEnterFunction f' lo args
										)
									| _ -> 
										(
											makeExpUndef args fdec;
											match lo with 
												| None -> (* no return value *) ()
												| Some(l) -> makeLvalUndef [l] fdec
										)
							)
						| _ -> ()
			) ilist
		| Return(eo, _) ->
			symExitFunction eo 
		| Break _ -> (* nothing to do *) ()
		| Continue _  -> (* nothing to do *) ()
		| If(e, thn, el, _) -> (* update path condition*)
			assert(index <> (-1)); 
			(
				match (handleBranchingStmt e true index) with
					| (true, e') -> 
						updatePathCondition e' s.sid index
					| _ -> ()
			)
		| Switch(e, bd, cases, _) -> (* update path condition*)
			assert(index <> (-1) && ((List.length cases) > index)); 
			let case = List.nth cases index in
			let labels = getSwitchCaseExpressions case in
			let elist = List.fold_left(
				fun expl label -> 
					let condition = BinOp(Eq, e, label, (typeOf e)) in
					match (handleBranchingStmt condition false index) with
						| (false, _) -> expl
						| (true, condition') -> 
							(
								match expl with
								| [] -> 
									[condition']
								| exp::rem -> 
									[BinOp(LOr, condition', exp, typeOf(e))]
							)
				) [] labels
			in
			if (List.length elist) > 0 then
				updatePathCondition (List.hd elist) s.sid index;
		| Loop _ -> (* nothing to do because it's a while(1) loop*) ()

let executeSymTrace (stmtInfo:(int * int) list) = 
	(*Log.log (Printf.sprintf "received %d statements\n" (List.length stmtInfo));*)
	symTraceInitialize();
	(* Temp limit on size of trace. Otherwise it takes too long to execute *)
	if (List.length stmtInfo) < Options.maxSymbolicStatements then (
		List.iter(
			fun (sid,index) -> 
				(*Log.log (Printf.sprintf "sid=%d, index=%d, tracePos=%d\n"
					sid index !currentTracePos);*)
				executeStmt sid index;
				incr currentTracePos
		)(List.rev stmtInfo);
	);
	savePCtoFile (ConfigFile.find Options.keySymPath)
;;
Callback.register "executeSymTrace" executeSymTrace;;