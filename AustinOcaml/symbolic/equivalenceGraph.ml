(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open Printf
open Pretty
open Symbolic
open Utils

module Log = LogManager

exception Infeasible

module IntSet = Set.Make (struct type t = int;; let compare = compare end)

module EquivalenceNode = Set.Make(
struct 
	type t = exp;; 
	let compare e1 e2 = 
		if Utils.compareExp (Expcompare.stripCastsDeepForPtrArith e1) (Expcompare.stripCastsDeepForPtrArith e2) then 0 else (
			let s1 = Pretty.sprint 255 (Cil.d_plainexp()e1) in
			let s2 = Pretty.sprint 255 (Cil.d_plainexp()e2) in
			compare s1 s2
		) 
end)

type eqNode = {id:int;mutable elements:EquivalenceNode.t;mutable edges:IntSet.t}

let uniqueID = ref 0
let eqGraph = ref []

let reset() = 
	uniqueID := 0;
	eqGraph := []
		
let emptyGraph () = eqGraph := []; uniqueID := 0
let makeNode (e:exp) = 
	incr uniqueID;
	{id=(!uniqueID);elements=(EquivalenceNode.singleton e);edges=IntSet.empty}

let mergeNodes (n1:eqNode) (n2:eqNode) = 
	(* assume n1 and n2 are not connected via an edge *)
	incr uniqueID;
	{id=(!uniqueID);elements=(EquivalenceNode.union n1.elements n2.elements);edges=(IntSet.union n1.edges n2.edges)}
	
let tryFindContainingNode (e:exp) = 
	let rec searchGraph (nodes:eqNode list) = 
		match nodes with
			| [] -> None
			| n::rem ->
				if EquivalenceNode.mem e n.elements then Some(n)
				else searchGraph rem 
	in
  searchGraph !eqGraph
	
let findOrCreateContainingNode (e:exp) = 
	let e' = if isZero e then zero else (stripCasts e) in
	match (tryFindContainingNode e') with
		| None -> 
			let n = makeNode e' in
			eqGraph := (n::(!eqGraph));
			n
		| Some(n) -> n
	
let hasEdge (e1:exp) (e2:exp) = 
	let no1 = tryFindContainingNode e1 in
	let no2 = tryFindContainingNode e2 in
	match no1,no2 with
		| None,_ -> false
		| _,None -> false
		| Some(n1),Some(n2) -> (
				(* check if either n1.edges contains n2.id*)
				(* or if n2.edges contains n1.id *)
				IntSet.mem n2.id n1.edges || IntSet.mem n1.id n2.edges
			)

let handleEqOp (e1:exp) (e2:exp) = 
	let n1 = findOrCreateContainingNode e1 in
	let n2 = findOrCreateContainingNode e2 in
	(* n1 and n2 must not have an edge *)
	if IntSet.mem n2.id n1.edges || IntSet.mem n1.id n2.edges then (
		Log.debug (Printf.sprintf "%s = %s is infeasible\n"
			(Pretty.sprint 255 (Cil.d_exp()e1))
			(Pretty.sprint 255 (Cil.d_exp()e2)));
		raise Infeasible
	)	else (
		(* merge elements into n3*)
		(* delete nodes n1 and n2 from eqGraph*)
		(* add node n3 to eqGraph *)
		let n3 = mergeNodes n1 n2 in
		eqGraph := List.filter(fun node -> node.id <> n1.id && node.id <> n2.id)(!eqGraph);
		eqGraph := (n3::(!eqGraph))
	)				

let handleNeOp (e1:exp) (e2:exp) = 
	let n1 = findOrCreateContainingNode e1 in
	let n2 = findOrCreateContainingNode e2 in
	(* n1 and n2 must not be the same node *)
	if n1.id = n2.id then (
		Log.debug (Printf.sprintf "%s != %s is infeasible\n"
			(Pretty.sprint 255 (Cil.d_exp()e1))
			(Pretty.sprint 255 (Cil.d_exp()e2)));
		raise Infeasible
	)	else (
		n1.edges <- IntSet.add n2.id n1.edges;
		n2.edges <- IntSet.add n1.id n2.edges
	)
		
let zeroNode () = 
	try
		List.find (
			fun node -> 
				EquivalenceNode.mem zero node.elements
		)(!eqGraph)
	with
		| Not_found -> (
				let n = makeNode zero in
				eqGraph := (n::(!eqGraph));
				n
			)
	
let containsZeroNode (n:eqNode) = 
	EquivalenceNode.mem zero n.elements
			
(* for each conj, find lvals that are inputs and whose lvalInfo.expr matches the conj*) 
let printGraph () =
	let doc = (++) ((++) (text (Printf.sprintf "EQ graph contains %d nodes" (List.length !eqGraph))) line) line in
	List.fold_left (
		fun doc' node ->  
			let d = ref ((++) ((++) doc' (text (Printf.sprintf "Node %d has %d elements" node.id (EquivalenceNode.cardinal node.elements)))) line) in
			(*IntSet.iter(
				fun id -> 
					d := (++) (!d) (text (Printf.sprintf "%d" id))
			)node.edges;*)
			EquivalenceNode.iter(
				fun e -> 
					d := (++) (!d) (text (Printf.sprintf "%s\n" (Pretty.sprint 255 (Cil.d_exp () e))))
			)node.elements;
			!d
	) doc !eqGraph

(********************************)
let rec expDependsOnMem (e:exp) = 
	let rec isPtrType (t:typ) = 
		match t with
			| TPtr(t', _) -> true
			| TNamed(ti, _) -> isPtrType ti.ttype
			| _ -> false
	in
	match e with
		| Const _ | SizeOf _ | SizeOfE _ | SizeOfStr _ | AlignOf _ | AlignOfE _ -> false
		| Lval l | AddrOf l | StartOf l -> 
			(* check *)
			isPtrType (unrollType (typeOfLval l))
		| UnOp(u, e', _) -> expDependsOnMem e'
		| BinOp(_, e1, e2, _) -> expDependsOnMem e1 || expDependsOnMem e2
		| CastE(_, e') -> expDependsOnMem e'

let rec findLvalConstsFromExp (e:exp) = (*SLOW*)
	if (isConstant e) then
		([], [e])
	else (
		((ExpHashtbl.fold(
			fun key value res -> 
				if (Utils.compareExp key e) then (key::res)
				else res
		)!state.s []),[])
	)

let rec prepareExprForGraph (e:exp) = 
	if (expDependsOnMem e) then (
		match e with
			| SizeOf _ | SizeOfE _ | SizeOfStr _ | AlignOf _ | AlignOfE _ -> (constFold true e)
			| UnOp(u, e', _) -> 
				(
					match u with
						| Neg -> Log.error (sprintf "Neg operator with pointer (%s)\n" (Pretty.sprint 255 (Cil.d_exp () e)))
						| BNot -> Log.error (sprintf "BNot operator with pointer (%s)\n" (Pretty.sprint 255 (Cil.d_exp () e)))
						| LNot -> 
							Utils.propagateNegation e
							(*(propagateNegation e')*)
				)
			| CastE(t, e') -> 
				CastE(t, (prepareExprForGraph e'))
			| _ -> e 
  ) else
		e
		
let rec addExpressionToGraph (e:exp) = 
	if (expDependsOnMem e) then (
		(* for each e, find its lval alias from symbolic trace *)
		(* in addition call findLvalConstsFromExp *)
		match e with
			| Const _ | Lval _ | AddrOf _ | StartOf _ -> 
				handleNeOp e zero
			| SizeOf _ | SizeOfE _ | SizeOfStr _ | AlignOf _ | AlignOfE _ -> 
				handleNeOp (constFold true e) zero
			| UnOp(u, e', _) -> 
				addExpressionToGraph (prepareExprForGraph e)
			| BinOp(b, e1, e2, _) -> 
				(
					if not(Utils.isComparisonOp b) then (
						(* e != 0 *)
						handleNeOp e zero
					) else (
						match b with
							| Eq -> (* e1 == e2 *)
								handleEqOp e1 e2
							| Ne -> 
								handleNeOp e1 e2
							| _ -> Log.warn (sprintf "Ignoring BinOp %s in pointer constraint\r\n" (Pretty.sprint 255 (Cil.d_binop () b)));
					)
				)
			| CastE(_, e') -> 
				handleNeOp (prepareExprForGraph e) zero
	)
;;