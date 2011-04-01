open Cil
open Utils

module Log = LogManager

type symbolic_state = {s : exp ExpHashtbl.t; u : exp ExpHashtbl.t}

let symStack : (lval option * symbolic_state) list ref = ref []

let state : symbolic_state ref = ref {s=ExpHashtbl.create 100; u=ExpHashtbl.create 10}

class rewriteVisitor = object(this)
	inherit nopCilVisitor
	method vexpr (e:exp) = 
		match e with
			| Lval(Mem _, NoOffset) -> 
				(
					try
						let e' = ExpHashtbl.find !state.s e in
						match (stripCasts e') with
							| AddrOf(l) -> ChangeTo (Lval(l))
							| _ -> ChangeTo e'
					with
						| Not_found -> DoChildren
				)
			| Lval(l) | StartOf(l) -> 
				(
					try
						let e' = ExpHashtbl.find !state.s e in
						ChangeTo e' 
					with
						| Not_found -> DoChildren
				)
			| _ -> DoChildren 
end
let rewriteExpression (e:exp) = 
	let vis = new rewriteVisitor in
	visitCilExpr vis e

class isUndefVisitor (result : bool ref) = object
	inherit nopCilVisitor
	method vexpr (e:exp) = 
		if (ExpHashtbl.mem !state.u e) then (
			result := true;
			SkipChildren
		) else
			DoChildren
end
let isExpUndefined (e:exp) = 
	let isUndef = ref false in
	let vis = new isUndefVisitor isUndef in
	ignore(visitCilExpr vis e);
	!isUndef

let makeExpUndefined (e:exp) (_state: symbolic_state) =
	ExpHashtbl.remove _state.s e;
	ExpHashtbl.replace _state.u e e
	
let unassign (l:lval) (_state: symbolic_state) = 
	makeExpUndefined (Lval(l)) _state
		
let assign (l:lval) (e:exp) = 
	let e' = rewriteExpression e in
	if (isExpUndefined e') then (
		Log.debug (Printf.sprintf "not updating lval %s because %s is considered undefined\n"
			(Pretty.sprint 255 (Cil.d_lval()l))
			(Pretty.sprint 255 (Cil.d_exp()e')));
		unassign l !state
	) else (
		ExpHashtbl.replace !state.s (Lval(l)) e'
	)

let call (lo:lval option) (fd:fundec) (args:exp list) =
  let new_state : symbolic_state = {s=ExpHashtbl.create 100; u=ExpHashtbl.create 10} in
	List.iter2(
		fun vi arg -> 
			let new_arg = rewriteExpression arg in
			if (isExpUndefined new_arg) then (
				ExpHashtbl.add new_state.u (Lval(var vi)) (Lval(var vi))
			) else (
				ExpHashtbl.add new_state.s (Lval(var vi)) new_arg
			)	
	)fd.sformals args;
	
	(* push current state onto stack *)
	symStack := (lo,!state)::!symStack;

	state := new_state
	
let return (eo:exp option) =
	if(List.length !symStack) > 0 then (
		let lo, old_state = List.hd !symStack in
		symStack := List.tl !symStack;
		(
			match lo, eo with
				| Some(l),Some(e) -> 
					let e' = rewriteExpression e in
					if (isExpUndefined e') then
						unassign l old_state
					else
						ExpHashtbl.replace old_state.s (Lval(l)) e'
				| _ -> ()
		);
		state := old_state
	)

let pruneState (tokeep : lval list) =
	let new_state = {s=ExpHashtbl.create 100;u=ExpHashtbl.create 10} in
	ExpHashtbl.iter(
		fun key value -> 
			if (List.exists (fun l -> Utils.compareExp key (Lval(l)))tokeep) then
				ExpHashtbl.add new_state.s key value;
	)!state.s;
	state := new_state
	
let currentState_to_string () = 
	ExpHashtbl.fold(
		fun key value res -> 
			res ^ (Printf.sprintf "%s -> %s\n"
				(Pretty.sprint 255 (Cil.d_exp()key))
				(Pretty.sprint 255 (Cil.d_exp()value)))
	)!state.s "symbolic state:\n"
	
let printCurrentState () = 
	Log.log (Printf.sprintf "%s" (currentState_to_string ()))

type atomicAlia = exp list (* each expr is joined by LAnd *)
type stmtConj = int*int*(atomicAlia list) (* each atomicAlia is joined by LOr *)
type pathCondition = {mutable conjuncts : stmtConj list; mutable pathExpression : exp}

let getStmtConditions (_,_,con) = con

let pc = {conjuncts = [];pathExpression = one}

let isUniqueStmtConjExpr (_,_,atomic) = 
	let f1 = List.flatten atomic in
	not(List.exists(
		fun (_,_,atomic') -> 
			let f2 = List.flatten atomic' in
			if (List.length f1) <> (List.length f2) then false
			else ( 
				List.exists2( fun e1 e2 -> Utils.compareExp e1 e2 ) f1 f2
			)
	)pc.conjuncts)
	
let updatePathCondition (conj:stmtConj)  = 
	if isUniqueStmtConjExpr conj then (
		pc.conjuncts <- (pc.conjuncts @ [conj])
	)
	
let printPathCondition () =
	let concatenateAtomicConditions (conditions:exp list) = 
		List.fold_left(
			fun res con -> 
				if res = Cil.one then 
					con
				else
					BinOp(LAnd, res, con, intType)
		)Cil.one conditions
	in
	let concatenateStmtConj (atomicConditions:atomicAlia list) = 
		List.fold_left(
			fun res alist -> 
				let atomicExpr = concatenateAtomicConditions alist in
				if res = Cil.one then
					atomicExpr
				else
					BinOp(LOr, res, atomicExpr, intType)
		)Cil.one atomicConditions
	in
	let pc_expr = 
		List.fold_left(
			fun cum_expr (_,_,atomics) -> 
				let con = concatenateStmtConj atomics in
				if cum_expr = Cil.one then
					con
				else
					BinOp(LAnd, cum_expr, con, intType)
		)Cil.one pc.conjuncts
	in 
	Log.log (Printf.sprintf "Path Condition: %s\n" (Pretty.sprint 255 (Cil.d_exp () pc_expr)))

let reset() = 
	symStack := [];
	ExpHashtbl.clear !state.s;
	ExpHashtbl.clear !state.u;
	pc.conjuncts <- [];
	pc.pathExpression <- one
	
let saveCurrentStateToFile () = 
	let outchan = open_out_bin (ConfigFile.find Options.keySymState) in
	Marshal.to_channel outchan !state [];
	close_out outchan
	
let loadStateFromFile () = 
	let fname = (ConfigFile.find Options.keySymState) in
	assert(Sys.file_exists fname);
	let inchan = open_in_bin fname in
  state := (Marshal.from_channel inchan : symbolic_state);
  close_in inchan

let savePathConditiontoFile () = 
	let outchan = open_out_bin (ConfigFile.find Options.keySymPath) in
  Marshal.to_channel outchan pc [];
  close_out outchan

let loadPathConditionfromFile () =
	let fname = (ConfigFile.find Options.keySymPath) in
	assert(Sys.file_exists fname);
	let inchan = open_in_bin fname in
  let saved = (Marshal.from_channel inchan : pathCondition) in
  close_in inchan;
	pc.conjuncts <- saved.conjuncts;
	pc.pathExpression <- saved.pathExpression
	