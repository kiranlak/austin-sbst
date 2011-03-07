(* Copyright: Kiran Lakhotia, University College London, 2011 *)
(* < set min as constant - 1*)
(* <= set min as constant*)
(* >,>= see above*)
(* == check if is pointer or arithmetic lval. If latter, set min,max to constant*)
(* != lval must be pointer *)
open Cil
open Utils

module Log = LogManager

let precons = ref []

let printPreconditions() = 
	List.iter(
		fun pre -> 
			Log.log (Printf.sprintf "precondition:%s\n"
				(Pretty.sprint 255 (Cil.d_exp()pre)));
	)!precons
	
let loadPreconditions () = 
	let inchan = open_in_bin (ConfigFile.find Options.keyPreconditionFile) in
  precons := (Marshal.from_channel inchan : exp list);
  close_in inchan
	
class expVisitor (currentLval : lval) (found:bool ref) = object
	inherit nopCilVisitor
	
	method vlval (l:lval) = 
		if (compareLvalByName l currentLval) then (
			found := true
		);
		SkipChildren
end

let rec getConstantFromExp (e:exp) = 
	match e with
		| Const(c) -> c
		| CastE(_,e') -> getConstantFromExp e'
		| _ -> Log.error (Printf.sprintf "Invalid constant exp (%s)\n" (Pretty.sprint 255 (Cil.d_exp()e)))

let castConstantAsI64 (c:constant) =
	match c with
		| CInt64(ival,_,_) -> ival
		| CChr(char) -> Int64.of_int (int_of_char char)
		| CReal(fval,_,_) -> Int64.of_float fval
		| _ -> Log.error (Printf.sprintf "Invalid constant (%s)\n" (Pretty.sprint 255 (Cil.d_const()c)))

let getConstantValueFromExp (e:exp) = 
	let c = getConstantFromExp e in
	castConstantAsI64 c

let getConstraintInfo (e:exp) = 
	match e with
		| BinOp(b, lhs, rhs, _) -> 
			(
				let constantValue =
					if (isConstant lhs) then getConstantValueFromExp lhs
					else if (isConstant rhs) then getConstantValueFromExp rhs
					else
						Log.error (Printf.sprintf "Must have a constant in precondition (%s)\n" (Pretty.sprint 255 (Cil.d_exp()e)))
				in
				(b, constantValue) 
			)
		| _ -> Log.error (Printf.sprintf "%s is not a BinOp\n" (Pretty.sprint 255 (Cil.d_exp()e)))
		
let getLvalPreconditions (l:lval) = 
	List.filter(
		fun pre -> 
			let lvalMatch = ref false in
			let vis = new expVisitor l lvalMatch in
			ignore(visitCilExpr vis pre);
			!lvalMatch
	)!precons
			
let getIntegralBounds (l:lval) = 
	let minOpt = ref None in
	let maxOpt = ref None in
	List.iter(
		fun pre ->
			let b, cons = getConstraintInfo pre in
			match b with
				| Lt -> maxOpt := Some (Int64.sub cons Int64.one)
				| Gt -> minOpt := Some (Int64.add cons Int64.one)
				| Le -> maxOpt := Some cons
				| Ge -> minOpt := Some cons
				| Eq -> maxOpt := Some cons; minOpt := Some cons
				| _ -> Log.error (Printf.sprintf "Invalid binop for integral precondition %s\n" (Pretty.sprint 255 (Cil.d_binop()b)))		
	)(getLvalPreconditions l);
	(!minOpt,!maxOpt)
	
let getFloatBounds (l:lval) = 
	let minOpt = ref None in
	let maxOpt = ref None in
	List.iter(
		fun pre ->
			let b, cons = getConstraintInfo pre in
			match b with
				| Lt -> maxOpt := Some (Int64.to_float (Int64.sub cons Int64.one))
				| Gt -> minOpt := Some (Int64.to_float (Int64.add cons Int64.one))
				| Le -> maxOpt := Some (Int64.to_float cons)
				| Ge -> minOpt := Some (Int64.to_float cons)
				| Eq -> maxOpt := Some (Int64.to_float cons); minOpt := Some (Int64.to_float cons)
				| _ -> Log.error (Printf.sprintf "Invalid binop for float precondition %s\n" (Pretty.sprint 255 (Cil.d_binop()b)))		
	)(getLvalPreconditions l);
	(!minOpt,!maxOpt)
	
let getPointerConstraint (l:lval) = 
	let constraints = (getLvalPreconditions l) in
	assert((List.length constraints) < 2);
	match constraints with
		| [] -> None
		| pre::tl -> (
			let b, cons = getConstraintInfo pre in
			if not(cons = Int64.zero) then 
				Log.error "Pointer preconditions may only be of the form p == (void*)0, p != (void*)0\n";
			match b with
				| Eq -> Some true
				| Ne -> Some false
				| _ -> Log.error (Printf.sprintf "Invalid binop for pointer precondition %s\n" (Pretty.sprint 255 (Cil.d_binop()b)))
			)
			