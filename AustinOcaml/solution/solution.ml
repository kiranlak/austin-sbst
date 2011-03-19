(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open Printf
open Utils
open BaseObjValue

module Log = LogManager
		
let uniqueSolutionId = ref 0
let uniqueNodeId = ref (-1)
let getNextUniqueNodeId () = 
	incr uniqueNodeId;
	!uniqueNodeId

let getNextUniqueSolutionId () = 
	incr uniqueSolutionId;
	!uniqueSolutionId
		
type intNode = 
{
	imin  : int64;
	imax  : int64;
	mutable ival  : int64;
}
type floatNode = 
{
	fmin : float;
	fmax : float;
	mutable fval  : float;
}
type pointerNode = 
{
	targetNodeTyp : typ;
	mutable targetNodeId : int;
	mutable pointToNull  : bool;
	mutable takesAddrOf  : bool;
	mutable isPointerToArray : bool;
	mutable firstArrayDim : int
}
type concreteValue =
{
	address : int64;
	offset  : int;
	width   : int;
}

type inputNode = IntNode of intNode | FloatNode of floatNode | PointerNode of pointerNode
and baseNode = 
{
	mutable bid : int;
	cilLval : lval;
	node : inputNode;
	mutable concreteVal : concreteValue option
}												
let rec cloneNode (n:baseNode) = 
	{bid=n.bid;cilLval=n.cilLval;node=(cloneInputNode n.node);concreteVal=None}
and cloneInputNode (n:inputNode) = 
	match n with
		| IntNode(n') -> IntNode({imin=n'.imin;imax=n'.imax;ival=n'.ival})
		| FloatNode(n') -> FloatNode({fmin=n'.fmin;fmax=n'.fmax;fval=n'.fval})
		| PointerNode(n') -> PointerNode({targetNodeTyp=n'.targetNodeTyp;targetNodeId=n'.targetNodeId;pointToNull=n'.pointToNull;takesAddrOf=n'.takesAddrOf;isPointerToArray=n'.isPointerToArray;firstArrayDim=n'.firstArrayDim})
			
let printNode (n:baseNode) = 
	match n.node with
		| IntNode(n') -> 
			Log.log (Printf.sprintf "%d - value: %s = %Ld ([%Ld,%Ld])\n"
				n.bid (Pretty.sprint 255 (Cil.d_lval () n.cilLval)) n'.ival
				n'.imin n'.imax)
		| FloatNode(n') -> 
			Log.log (Printf.sprintf "%d - value: %s = %.10f ([%.5f,%.5f])\n"
				n.bid (Pretty.sprint 255 (Cil.d_lval () n.cilLval)) n'.fval n'.fmin n'.fmax)
		| PointerNode(n') -> 
			Log.log (Printf.sprintf "%d - %s:pointsToType=%s,tid=%d,isNull=%B,addrOf=%B\n"
				n.bid (Pretty.sprint 255 (Cil.d_plainlval () n.cilLval)) 
				(Pretty.sprint 255 (Cil.d_type () n'.targetNodeTyp))
				n'.targetNodeId n'.pointToNull n'.takesAddrOf	
				)

type savedSolution = 
{
	_sid : int;
	_inputs : baseNode list;
	_fitness : objectiveValue;
	_ideal : bool;				
}
	
class candidateSolution = object(this)
	val mutable solutionId = getNextUniqueSolutionId()
	val mutable numInputs = 0
	val mutable revInputList = []
	val mutable fitness : objectiveValue = Simple(max_float)
	val mutable isIdeal = false
	val lvalNodeMappings : baseNode LvalHashtbl.t = LvalHashtbl.create 100
			
	method init (sol:candidateSolution) = 
		solutionId <- sol#getSolutionId();
		fitness <- sol#getFitness();
		isIdeal <- sol#isIdeal();
		revInputList <- [];
		LvalHashtbl.clear lvalNodeMappings;
		List.iter(
			fun node -> 
				let clone = cloneNode node in
				this#appendNode clone;
				LvalHashtbl.add lvalNodeMappings clone.cilLval clone	
		)(sol#getInputList());
		numInputs <- sol#getNumInputs()
	
	method setSolutionId (id:int) = 
		solutionId <- id
				
	method setFitness (f:objectiveValue) (ideal:bool) = 
		isIdeal <- ideal;
		fitness <- f
		
	method getFitness () : objectiveValue = fitness
	method isIdeal() : bool = isIdeal
	method getInputList () : baseNode list = List.rev revInputList
	method getRevInputList() : baseNode list = revInputList
	method getNumInputs() : int = numInputs
	method getSolutionId() : int = solutionId
	
	method appendNode (n:baseNode) = 
		revInputList <- (n::revInputList);
		numInputs <- numInputs + 1;
		LvalHashtbl.replace lvalNodeMappings n.cilLval n
	
	(* @unused *)
	method replaceEqualNode (old:baseNode) (new_node:baseNode) = (* fast *)
		match old.node,new_node.node with
			| IntNode(o),IntNode(n) -> o.ival <- n.ival
			| FloatNode(o),FloatNode(n) -> o.fval <- n.fval
			| PointerNode(o),PointerNode(n) -> 
				o.targetNodeId <- n.targetNodeId;
				o.pointToNull <- n.pointToNull;
				o.takesAddrOf <- n.takesAddrOf;
			| _,_ -> Log.error "Node mismatch, cannot replace\n"
	
	(* @unused *)
	method replaceNode (old:baseNode) (new_node:baseNode) = (* slow *)
		let rec searchList pre nodes = 
			match nodes with
				| [] -> Log.error "Failed to find node\n"
				| hd::tl ->
					if hd.bid = old.bid then (
						revInputList <- (pre @ (new_node::tl));
						LvalHashtbl.remove lvalNodeMappings old.cilLval;
						LvalHashtbl.replace lvalNodeMappings new_node.cilLval new_node;
					) else
						searchList (pre @ [hd]) tl
		in
		searchList [] revInputList
	
	(* @unused *)		
	method insertNodeAt (pos:int) (new_node:baseNode) = 
		let rec searchList pre nodes cnt = 
			match nodes with
				| [] -> revInputList <- (revInputList @ [new_node]); LvalHashtbl.replace lvalNodeMappings new_node.cilLval new_node
				| hd::tl -> 
					if cnt = pos then (
						revInputList <- (pre @ (new_node::tl));
						numInputs <- (List.length revInputList);
						LvalHashtbl.replace lvalNodeMappings new_node.cilLval new_node
					) else
						searchList (pre @ [hd]) tl (cnt + 1)
		in
		searchList [] revInputList 0
		
	method getNodeAt (pos:int) = 
		assert(pos >= 0 && pos < numInputs);
		List.nth revInputList pos
	
	(* @unused *)
	method removeNode (l:lval) = 
		let nopt = this#tryFindNodeFromLval l in
		match nopt with
			| Some(node) -> 
				let rec searchList pre nodes = 
					match nodes with
						| [] -> 
							Log.error (Printf.sprintf "Inconsistency between inputList and hash table (%s)\n" (Pretty.sprint 255 (Cil.d_lval()l)))
						| hd::tl -> 
							if hd.bid = node.bid then (
								revInputList <- (pre @ tl);
								numInputs <- (List.length revInputList);
								LvalHashtbl.remove lvalNodeMappings hd.cilLval
							) else (
								searchList (pre@[hd]) tl
							)
				in
				searchList [] revInputList
			| _ -> Log.warn (Printf.sprintf "Could not find node for %s\n" (Pretty.sprint 255 (Cil.d_lval()l))) 
	
	method tryFindNodeFromLval (l:lval) = 
		try
			Some(LvalHashtbl.find lvalNodeMappings l)
		with
			| Not_found -> 
				(
					try
						Some(LvalHashtbl.find lvalNodeMappings (normalizeArrayAccess l))
					with
						| Not_found -> None
				)
	
	method tryFindNodeFromNodeId (id:int) = 
		let rec searchList nodes = 
			match nodes with
				| [] -> None
				| hd::tl -> 
					if hd.bid = id then (
						Some(hd)
					) else
						searchList tl
		in
		searchList revInputList
	
	method findNodeIdFromLval (l:lval) = 
		let nodeOpt = this#tryFindNodeFromLval l in
		match nodeOpt with
			| Some(n) -> n.bid
			| _ -> Log.error (Printf.sprintf "Failed to find node for %s\n" (Pretty.sprint 255 (Cil.d_lval()l)))	
	
	method findNodeFromNodeId (id:int) = 
		List.find(fun n -> n.bid = id)revInputList
		
	method saveToFile (fname:string) = 
		let s = {_sid=solutionId;_inputs=revInputList;_fitness=fitness;_ideal=isIdeal} in
		let outchan = open_out_bin fname in
	  Marshal.to_channel outchan s [];
	  close_out outchan
	
	method loadFromFile (fname:string) = 
		let inchan = open_in_bin fname in
	  let saved : savedSolution = ((Marshal.from_channel inchan) : savedSolution) in
	  close_in inchan;
		solutionId <- saved._sid;
		revInputList <- saved._inputs;
		numInputs <- (List.length revInputList);
		fitness <- saved._fitness;
		isIdeal <- saved._ideal;
		List.iter(
			fun node -> LvalHashtbl.add lvalNodeMappings node.cilLval node
		)revInputList

	method removeAllNodes () = 
		revInputList <- [];
		numInputs <- 0;
		LvalHashtbl.clear lvalNodeMappings
	
	method print () = 
		let header = "Solution "^(fitness_to_string fitness)^":\n" in
		Log.log header;
		List.iter(
			fun node -> printNode node
		)(List.rev revInputList);
		Log.log "------\n"
end	

let mkIntNode (min:int64) (max:int64) (value:int64) (l:lval) = 
	let n = IntNode({imin=min;imax=max;ival=value}) in
	{bid=(getNextUniqueNodeId());cilLval=l;node=n;concreteVal=None}
	
let mkFloatNode (min:float) (max:float) (value:float) (l:lval) = 
	let n = FloatNode({fmin=min;fmax=max;fval=value}) in
	{bid=(getNextUniqueNodeId());cilLval=l;node=n;concreteVal=None}
	
let mkPtrNode (targetTyp:typ) (tid:int) (isNull:bool) (addrOf:bool) (isPtrToArray:bool) (firstDim:int) (l:lval) = 
	let n = PointerNode({targetNodeTyp=targetTyp;targetNodeId=tid;pointToNull=isNull;takesAddrOf=addrOf;isPointerToArray=isPtrToArray;firstArrayDim=firstDim}) in
	{bid=(getNextUniqueNodeId());cilLval=l;node=n;concreteVal=None}
	
let cloneSolution (sol:candidateSolution) = 
	let sol' = new candidateSolution in
	sol'#init sol;
	sol'
	
let saveCandidateSolutionToFile (sol : candidateSolution) : unit = 
	sol#saveToFile (ConfigFile.find Options.keyBinSolName)

let loadCandidateSolutionFromFile () : candidateSolution = 
	let sol = new candidateSolution in
	sol#loadFromFile (ConfigFile.find Options.keyBinSolName);
	sol

let solutionArchive : (string * candidateSolution) list ref = ref []
let addSolutionToArchive (comment:string) (sol:candidateSolution) = 
	solutionArchive := ((comment, (cloneSolution sol))::!solutionArchive)
		
let reset () = 
	uniqueSolutionId := 0;
	uniqueNodeId := (-1)
