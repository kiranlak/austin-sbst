(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil

open AustinRand
open Solution
open ArrayInputs
open Utils
module Log = LogManager
		
let round (v:float) (prec:float) = 
	let remainder = mod_float v prec in
	if (remainder > (0.5 *. prec)) then
		v -. remainder +. prec
	else
		v -. remainder
		
let truncate_float (v:float) (digits:float) = 
	let stepper = 10.0 ** digits in
	let i = truncate (v *. stepper) in
	(float_of_int i) /. stepper

let computeBigIntBounds (bits:int) (signed:bool) = 
	let shifted = Big_int.power_int_positive_int 2 bits in
	let two_big_int = Big_int.big_int_of_int 2 in
	let half = Big_int.div_big_int shifted two_big_int in
	let lower = 
		if signed then (Big_int.minus_big_int half) else Big_int.zero_big_int
	in
	let upper = 
		if signed then (Big_int.sub_big_int half Big_int.unit_big_int) else (Big_int.sub_big_int shifted Big_int.unit_big_int)
	in
	(lower,upper)

let computeIntegralBounds (l:lval) (signed:bool) = 
	let bits = Utils.getLvalBits l in
	let bmin,bmax = computeBigIntBounds bits signed in
	(Big_int.int64_of_big_int bmin, Big_int.int64_of_big_int bmax)
		
let makeIntNode (kind:ikind) (l:lval) = 
	let minOpt,maxOpt = Preconditions.getIntegralBounds l in
	let minType,maxType = 
		match kind with
			| IBool -> Int64.zero,Int64.one
			| _ -> computeIntegralBounds l (isSigned kind) 
	in
	let min,max = 
		match minOpt,maxOpt with
			| Some(_min),Some(_max) -> _min,_max
			| Some(_min),None -> _min,maxType
			| None, Some(_max) -> minType,_max
			| None, None -> minType,maxType 
	in
	let value = 
		let _min,_max = 
			match (Preconditions.getInitialValueRestrictions l) with
				| Some(_min'),Some(_max') -> (Int64.of_float _min'),(Int64.of_float _max')
				| Some(_min'),None -> (Int64.of_float _min'),max
				| None, Some(_max') -> min,(Int64.of_float _max')
				| None, None -> min,max
		in 
		AustinRand.nextInt64 ~lower:_min _max 
	in
	mkIntNode min max value l
			
let gaussian (mean:float) (stdev:float) = 
	let u = AustinRand.nextFloat 1.0 in
	let v = AustinRand.nextFloat 1.0 in
	let pi = 4.0 *. Pervasives.atan 1.0 in
	let g = Pervasives.sin(2.0 *. pi *. v) *. Pervasives.sqrt(((-2.0) *. Pervasives.log(1.0 -. u))) in
	mean +. (stdev *. g)
	
let makeFloatNode (l:lval) = 
	let minOpt,maxOpt = Preconditions.getFloatBounds l in
	let min,max = 
		match minOpt,maxOpt with
			| Some(_min),Some(_max) -> _min,_max
			| Some(_min),_ -> _min,1.0
			| _,Some(_max) -> (float_of_int min_int),_max
			| _,_ -> (float_of_int min_int),(float_of_int max_int)
	in
	let value = 
		match (Preconditions.getInitialValueRestrictions l) with
			| Some(_min),Some(_max) -> 
				AustinRand.nextFloat ~lower:_min _max
			| Some(_min),None -> 
				if _min > 0.0 then 
					AustinRand.nextFloat ~lower:_min 1.0
				else
					gaussian 0.0 1.0
			| None, Some(_max) -> 
				if _max < 1.0 then 
					AustinRand.nextFloat ~lower:0.0 _max
				else
					gaussian 0.0 1.0
			| None, None -> gaussian 0.0 1.0
	in
	mkFloatNode min max value l
	
let baseLvals : (lval list ref) = ref []

let saveBaseLvalsToFile() = 
	let outchan = open_out_bin (ConfigFile.find Options.keyBaseLvalsFile) in
  Marshal.to_channel outchan !baseLvals [];
  close_out outchan
	
let loadBaseLvalsFromFile() = 
	let inchan = open_in_bin (ConfigFile.find Options.keyBaseLvalsFile) in
  baseLvals := (Marshal.from_channel inchan : lval list);
  close_in inchan
		
let unassignedPointers : baseNode list ref = ref []
let initializePointers : bool ref = ref false

let isPointerTargetNull (l:lval) (sol:candidateSolution) = 
	let nodeOpt = sol#tryFindNodeFromLval l in
	match nodeOpt with
		| Some(n) ->
			(
				match n.node with
					| PointerNode(pn) -> (n.bid, pn.pointToNull)
					| _ -> Log.error (Printf.sprintf "%s is not a pointer node\n" (Pretty.sprint 255 (Cil.d_lval()l)))
			) 
		| _ -> Log.error (Printf.sprintf "Failed to find node for %s\n" (Pretty.sprint 255 (Cil.d_lval()l)))
			
let getPotentialPointerTargets (plval:lval) (t:typ) (sol:candidateSolution) : ((baseNode * int) list) = 
	let host = typeSig t in
	let hostTarget = 
		match (unrollType t) with
			| TPtr(t',_) -> typeSig t'
			| _ -> 
				Log.error (Printf.sprintf "%s is not a pointer type\r\n" (Pretty.sprint 255 (Cil.d_type () (unrollType t))))
	in
	let isBitField (lh,off) = 
		Utils.isBitfield off
	in
	List.fold_left(
		fun res node -> 
			if not(Utils.compareLval node.cilLval plval) then (
				let target = typeSig (typeOfLval node.cilLval) in
				if (host = target) then (
					((node,0)::res) 
				) else if (hostTarget = target) then (
					if (not(isBitField node.cilLval)) then
						((node,1)::res)
					else
						res
				) else
					res
			) else
				res
	)[](sol#getRevInputList())
	
let clearUnassignedPointerList (sol:candidateSolution) = 
	List.iter(
		fun node -> 
			match node.node with
				| PointerNode(n) -> 
					(
						let targets = getPotentialPointerTargets node.cilLval (typeOfLval node.cilLval) sol in
						let length = List.length targets in
						if length = 0 then (
							n.targetNodeId <- (-1);
							n.pointToNull <- true;
							n.takesAddrOf <- false;
						) else (
							let targetNode, addrOf = List.nth targets (AustinRand.nextInt length) in
							if addrOf = 1 then (
								n.pointToNull <- false;
								n.targetNodeId <- (sol#findNodeIdFromLval targetNode.cilLval);
								n.takesAddrOf <- true;
							) else (
								let _id,_isNull = isPointerTargetNull targetNode.cilLval sol in
								n.pointToNull <- _isNull;
								n.targetNodeId <- _id;
							)
						)
					)
				| _ -> Log.error "Internal AUSTIN error:clearUnassignedPointerList contains non pointer node\n"
	)!unassignedPointers;
	unassignedPointers := []
	
let mkPointerToArray todo (l:lval) (at:typ) (alen:int) (solOpt:candidateSolution option) = 
	if not(isCompleteType_Austin at) then []
	else (
		let rec mkArrayItems cnt res = 
			if cnt >= alen then (
				res
			) else (
				let arrayAccess = 
					makeArrayAccess l (integer cnt)
					(*Mem(BinOp(IndexPI, (Lval(l)), (integer cnt), (typeOfLval l))), NoOffset*) 
				in
				mkArrayItems (cnt + 1) (res@(todo arrayAccess at solOpt))
			)
		in
		mkArrayItems 0 []
	)
		
let mkArray todo (l:lval) (at:typ) (alen:int) (solOpt:candidateSolution option) = 
	if not(isCompleteType_Austin at) then []
	else (
		let rec mkArrayItems cnt res = 
			if cnt >= alen then (
				res
			) else (
				let l' = Utils.normalizeArrayAccess (addOffsetLval (Index((integer cnt), NoOffset)) l) in
				mkArrayItems (cnt + 1) (res@(todo l' at solOpt))
			)
		in
		mkArrayItems 0 []
	)
	
let correctNodeIds (sol:candidateSolution) = 
	let indx = ref 0 in
	let mapping : (int,int) Hashtbl.t = Hashtbl.create (sol#getNumInputs()) in
	let inputs = sol#getInputList() in
	List.iter(
		fun node -> 
			if node.bid <> (!indx) then (
				Hashtbl.add mapping node.bid !indx
			);
			node.bid <- !indx;
			incr indx
	)inputs;
	List.iter(
		fun node -> 
			match node.node with
				| PointerNode(pn) -> 
					(
						if pn.targetNodeId >= 0 then (
							try
								let nid = Hashtbl.find mapping pn.targetNodeId in
								pn.targetNodeId <- nid
							with
								| Not_found -> () 
						)
					)
				| _ -> ()
	)inputs
				
let rec mkNewBaseNodeList (l:lval) (t:typ) (solOpt:candidateSolution option) = 
	if not(isCompleteType_Austin t) then []
	else (
		match t with
			| TInt(ikind,_) -> [makeIntNode ikind l]
			| TFloat(fkind,_) -> [makeFloatNode l]
			| TPtr(pt,attrs) -> 
				(
					if (isFunctionType (unrollType pt)) || not(isCompleteType_Austin pt) then []
					else (
						match (isArrayInput l) with
							| Some(al,at,adim) -> 
								(*let node = mkPtrNode at (-1) false false true (exp_to_int adim) l in*)
								(mkPointerToArray mkNewBaseNodeList l pt (exp_to_int adim) None)
							| None -> (
								match (Preconditions.getPointerConstraint l) with
									| Some tonull -> 
										if tonull then
											[mkPtrNode pt (-1) true false false 0 l]
										else (
											let node = mkPtrNode pt (-1) false false false 0 l in
											(node::(mkNewBaseNodeList (Mem(Lval(l)), NoOffset) pt None))
										)
									| None -> (
										if !initializePointers then (
											if AustinRand.tossCoin() then (
												if AustinRand.tossCoin() then (
													let node = mkPtrNode pt (-1) false false false 0 l in
													(node::(mkNewBaseNodeList (Mem(Lval(l)), NoOffset) pt None))
												) else (
													let node = mkPtrNode pt (0) false false false 0 l in
													unassignedPointers := (node::(!unassignedPointers));
													[node]
												)
											) else (
												[mkPtrNode pt (-1) true false false 0 l]
											)
										) else (
											[mkPtrNode pt (-1) true false false 0 l]
										)
									)
								)
					)
				)
			| TArray(at, lengthO, _) ->
				(mkArray mkNewBaseNodeList l at (lenOfArray lengthO) None)
			| TFun _ -> 
				Log.error "TFun in solution generator\n"
			| TNamed(ti,_) -> 
				(mkNewBaseNodeList l ti.ttype None)
			| TComp(ci,_) -> 
				List.fold_left(
					fun res field -> 
						let l' = addOffsetLval (Field(field, NoOffset)) l in
						(res@(mkNewBaseNodeList l' field.ftype None))
				)[] ci.cfields
			| TEnum(ei,_) -> 
				let len = Int64.of_int (List.length ei.eitems) in
				let value = AustinRand.nextInt64 len in
				[mkIntNode Int64.zero len value l]
			| _ -> (* ignore input *)[]
	)
	
let rec mkUpdatedBaseNodeList (l:lval) (t:typ) (solOpt:candidateSolution option) =
	let sol = 
		match solOpt with 
			| None -> Log.error "Must provide candidate solution to update\n"
			| Some(s) -> s
	in
	if not(isCompleteType_Austin t) then []
	else (
		match t with
			| TInt _ | TFloat _ | TEnum _  -> 
				(
					match sol#tryFindNodeFromLval l with
						| None -> mkNewBaseNodeList l t None
						| Some(n) -> [n]
				)
			| TPtr(pt,_) -> 
				let node = sol#tryFindNodeFromLval l in
				(
					match node with
						| None ->
							mkNewBaseNodeList l t None
						| Some(n) -> 
							(
								match n.node with
									| PointerNode(pn) -> 
										(
											if pn.isPointerToArray then (
												(n::(mkPointerToArray mkUpdatedBaseNodeList n.cilLval pn.targetNodeTyp pn.firstArrayDim solOpt))
											) else if not(pn.pointToNull) && pn.targetNodeId = (-1) then (
												(n::(mkUpdatedBaseNodeList (Mem(Lval(n.cilLval)), NoOffset) pn.targetNodeTyp solOpt))
											) else (
												[n]
											)								
										)
									| _ -> []
							)
				)
			| TArray(at, lengthO, _) ->
				(mkArray mkUpdatedBaseNodeList l at (lenOfArray lengthO) solOpt)
			| TFun _ -> Log.error "TFun in solution generator\n"
			| TNamed(ti,_) -> 
				(mkUpdatedBaseNodeList l ti.ttype solOpt)
			| TComp(ci,_) -> 
				List.fold_left(
					fun res field -> 
						let l' = addOffsetLval (Field(field, NoOffset)) l in
						(res@(mkUpdatedBaseNodeList l' field.ftype solOpt))
				)[] ci.cfields
			| _ -> (* ignore input *)[]
		)
			
let generateNewRandomSolution() = 
	let sol = new candidateSolution in
	List.iter(
		fun lv -> 
			let baseNodes = mkNewBaseNodeList lv (typeOfLval lv) None in
			List.iter(
				fun node -> sol#appendNode node
			)baseNodes
	)!baseLvals;
	clearUnassignedPointerList sol;
	sol
		
let generateUpdatedSolution (sol:candidateSolution) = 
	let nodes = 
		List.fold_left(
			fun res lv -> 
				let baseNodes = mkUpdatedBaseNodeList lv (typeOfLval lv) (Some sol) in
				(res @ baseNodes)
		)[] !baseLvals 
	in
	sol#removeAllNodes();
	List.iter(
		fun n -> sol#appendNode n
	)nodes;
	correctNodeIds sol;
	sol
