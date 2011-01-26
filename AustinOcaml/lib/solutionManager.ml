(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open Options
open Solution
open MainLib

module Log = LogManager

let nodeIndex = ref (-1)
let getNextNodeIndex () = 
	incr nodeIndex;
	!nodeIndex
	
let getNextPODNode (address:string) (offset:int) (width:int) = 
	let index = getNextNodeIndex() in
	assert(index < (List.length !inputNodes));
	let node = List.nth !inputNodes index in
	node.concreteVal <- (Some({address=(Int64.of_string address);offset=offset;width=width}));
	match node.node with
		| IntNode(_in) -> 
			Int64.to_float _in.ival
		| FloatNode(_fn) -> 
			_fn.fval
		| _ -> Log.error "Expected POD node but got pointer\n" 

let getNextPointerNode (address:string) = 
	let index = getNextNodeIndex() in
	assert(index < (List.length !inputNodes));
	let node = List.nth !inputNodes index in
	node.concreteVal <- (Some({address=(Int64.of_string address);offset=0;width=0}));
	match node.node with
		| PointerNode(pn) ->
			(index, pn.targetNodeId,pn.pointToNull,pn.takesAddrOf) 
		| _ -> Log.error "Expected pointer node but got POD\n"
;;
Callback.register "getNextPODNode" getNextPODNode;;
Callback.register "getNextPointerNode" getNextPointerNode;;