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
let inits = ref []

let savePreconditionsToFile () = 
	let revPre : exp list = List.rev !precons in
	let revInt : exp list = List.rev !inits in
	let outchan = open_out_bin (ConfigFile.find Options.keyPreconditionFile) in
  Marshal.to_channel outchan (revPre,revInt) [];
  close_out outchan
	
let loadPreconditionsFromFile () = 
	let inchan = open_in_bin (ConfigFile.find Options.keyPreconditionFile) in
  let pre,_inits = (Marshal.from_channel inchan : (exp list*exp list)) in
	precons := pre;
	inits := _inits;
  close_in inchan
	
let printPreconditions() = 
	List.iter(
		fun pre -> 
			Log.log (Printf.sprintf "precondition:%s\n"
				(Pretty.sprint 255 (Cil.d_exp()pre)));
	)!precons
	
let printInitPrecons() = 
	List.iter(
		fun pre -> 
			Log.log (Printf.sprintf "initial value restrictions:%s\n"
				(Pretty.sprint 255 (Cil.d_exp()pre)));
	)!inits
	
class expVisitor (currentLval : lval) (found:bool ref) = object
	inherit nopCilVisitor
	
	method vlval (l:lval) = 
		if (compareLval l currentLval) then (
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
		
		
let getLvalRestrictions (l:lval) (tosearch:exp list) = 
	List.filter(
		fun pre -> 
			let lvalMatch = ref false in
			let vis = new expVisitor l lvalMatch in
			ignore(visitCilExpr vis pre);
			!lvalMatch
	)tosearch
	
let getLvalPreconditions (l:lval) = 
	getLvalRestrictions l !precons

let getLvalInits (l:lval) = 
	getLvalRestrictions l !inits
						
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
	let constraints = getLvalPreconditions l in
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

let getInitialValueRestrictions (l:lval) = 
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
				| _ -> Log.error (Printf.sprintf "Invalid binop for initial precondition %s\n" (Pretty.sprint 255 (Cil.d_binop()b)))		
	)(getLvalInits l);
	(!minOpt,!maxOpt)
	 
class preconVisitor = object(this)
	inherit nopCilVisitor
				
	method vinst (i:instr) = 
		match i with
			| Call(lo, fname, args, _) -> 
				(
					let str_fname = 
						match (stripCasts) fname with
							| Lval(l) -> 
								(
									match l with
										| Var vi, _ -> vi.vname
										| _ -> ""
								)
							| _ -> ""
					in
					if str_fname = "Austin__Assume" || str_fname = "Austin__Assume__Init" then (
						let toadd = 
							List.fold_left(
								fun res arg ->
									match arg with
										| BinOp _ -> 
											( 
												(arg::res)
											)
										| _ -> 
											(
												Log.warn "Precondition argument does not appear to be of type BinOp, ignoring it!";
												res
											)
							) [] (List.tl args)
						in
						if str_fname = "Austin__Assume" then
							precons := List.rev_append toadd !precons
						else
							inits := List.rev_append toadd !inits
					);
				);
				SkipChildren
			| _ -> DoChildren		
end
	
class updateAAProto = object(this)
	inherit nopCilVisitor
	
	method vglob (g:global) = 
		match g with
			| GVar(v,ini,loc) -> 
				if v.vname = "Austin__Assume" || v.vname = "Austin__Assume__Init" then (
					v.vattr <- [];
					v.vtype <- TFun(voidType,Some[("argc",uintType,[])],true,[]);
					SkipChildren
				) else DoChildren
			| _ -> DoChildren
end
let collectPreconditions (source:file) (fut:fundec) = 
	let vis = new preconVisitor in
	ignore(visitCilFunction vis fut);
	savePreconditionsToFile ();
	precons := [];
	inits := [];
	(* update any Austin__Assume prototype *)
	let vis' = new updateAAProto in
	visitCilFile vis' source
			