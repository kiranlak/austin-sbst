(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil

open AustinRand
open Solution

module Log = LogManager

let solutionArchive : (string * candidateSolution) list ref = ref []
let addSolutionToArchive (comment:string) (sol:candidateSolution) = 
	solutionArchive := ((comment, (cloneSolution sol))::!solutionArchive)
	
let reset() = 
	solutionArchive := []
	
let createTestCasesFromArchive (testdrv:fundec) (fut:fundec) = 
	ignore(List.fold_left(
		fun id (comment,sol) -> 
			ignore(TestCaseWriter.saveCandidateSolution id sol comment testdrv fut);
			(id + 1)
	) 1 (!solutionArchive))
	
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
	match kind with
		| IChar | ISChar | IInt | IShort | ILong | ILongLong -> 
			let min,max = computeIntegralBounds l true in
			let value = AustinRand.nextInt64 ~lower:min max in
			mkIntNode min max value l
		| IUChar | IUInt | IUShort | IULong | IULongLong -> 
			let min,max = computeIntegralBounds l false in
			let value = AustinRand.nextInt64 max in
			mkIntNode min max value l
		| IBool -> 
			let value = if AustinRand.tossCoin() then Int64.one else Int64.zero in
			mkIntNode Int64.zero Int64.one value l
			
let gaussian (mu:float) (sigma:float) = 
	let u = AustinRand.nextFloat 1.0 in
	let v = AustinRand.nextFloat 1.0 in
	let pi = 4.0 *. Pervasives.atan 1.0 in
	let g = Pervasives.sin(2.0 *. pi *. v) *. Pervasives.sqrt(((-2.0) *. Pervasives.log(1.0 -. u))) in
	mu +. (sigma *. g)
	
let generateRandomFloatVal () = 
	gaussian 0.0 1.0
	
class changeVidVisitor (pairs:(varinfo*varinfo)list) = object(this)
	inherit nopCilVisitor

	method vvrbl (v:varinfo) = 
		try
			let oldV,newV = List.find(fun (o,n) -> o.vid = v.vid)pairs in
			ChangeTo newV
		with
			| Not_found -> DoChildren
end
		
type structuredInput = Leaf of baseNode | Node of baseNode * structuredInput list
class listToStructuredInputsConverter (testDriver:fundec) = object(this)
	
	method private mkPointerToArray (l:lval) (arrayType:typ) (arrayLength:int) (sol:candidateSolution) =
		let rec mkArrayItems cnt res = 
			if cnt >= arrayLength then (
				res
			) else (
				mkArrayItems (cnt + 1) (res@(this#mkStructuredLists (Mem(BinOp(IndexPI, (Lval(l)), (integer cnt), arrayType)), NoOffset) arrayType sol))
			)
		in
		mkArrayItems 0 []
		
	method private mkArray (l:lval) (arrayType:typ) (arrayLength:int) (sol:candidateSolution) =
		let rec mkArrayItems cnt res = 
			if cnt >= arrayLength then (
				res
			) else (
				let l' = addOffsetLval (Index((integer cnt), NoOffset)) l in
				mkArrayItems (cnt + 1) (res@(this#mkStructuredLists l' arrayType sol))
			)
		in
		mkArrayItems 0 []
		
	method private mkStructuredLists (l:lval) (t:typ) (sol:candidateSolution) = 
		match t with
			| TInt _ | TFloat _ | TEnum _  -> 
				(
					match sol#tryFindNodeFromLval l with
						| None -> Log.error (Printf.sprintf "Could not find lval %s\n" (Pretty.sprint 255 (Cil.d_lval()l)))
						| Some(n) -> [Leaf(n)]
				)
			| TPtr(pt,_) -> 
				let node = sol#tryFindNodeFromLval l in
				(
					match node with
						| None -> Log.error (Printf.sprintf "Could not find lval %s\n" (Pretty.sprint 255 (Cil.d_lval()l)))
						| Some(n) -> 
							(
								match n.node with
									| PointerNode(pn) -> 
										(
											if pn.isPointerToArray then (
												[(Node(n, (this#mkPointerToArray n.cilLval pn.targetNodeTyp pn.firstArrayDim sol)))]
											) else if not(pn.pointToNull) && pn.targetNodeId = (-1) then (
												[(Node(n, (this#mkStructuredLists (Mem(Lval(n.cilLval)), NoOffset) pn.targetNodeTyp sol)))]
											) else (
												[Leaf(n)]
											)
										)
									| _ -> Log.error "Non pointer node of type TPtr\n"
							)
				)
			| TArray(at, lengthO, _) -> 
				(
					(this#mkArray l at (lenOfArray lengthO) sol)
				)
			| TFun _ -> Log.error "TFun in solution unflatten\n"
			| TNamed(ti,_) -> 
				(this#mkStructuredLists l ti.ttype sol)
			| TComp(ci,_) -> 
				List.fold_left(
					fun res field -> 
						let l' = addOffsetLval (Field(field, NoOffset)) l in
						(res@(this#mkStructuredLists l' field.ftype sol))
				)[] ci.cfields
			| _ -> (* ignore input *)[]
	
	method private handleInstructions (ilist:instr list) (sol:candidateSolution) = 
		List.fold_left(
			fun res i -> 
				match i with
					| Call(lo, fcall, args, _) -> 
						(
							match lo with
								| Some(l) -> 
									(
										(res @ (this#mkStructuredLists l (typeOfLval l)) sol)
									)
								| _ -> res
						)
					| _ -> res	
		)[] ilist
		
	method start(sol:candidateSolution) =
		let rec walkStatements (stmts:stmt list) (res:structuredInput list) = 
			match stmts with
				| [] -> res
				| s::rem -> 
					(
						match s.skind with
							| Instr(ilist) -> 
								walkStatements rem (res @ (this#handleInstructions ilist sol))
							| Block(b) -> 
								let res' = walkStatements b.bstmts [] in
								walkStatements rem (res @ res')
							| _ -> walkStatements rem res
					)
		in
		walkStatements testDriver.sbody.bstmts []
		
	method flatten (inputs:structuredInput list) = 
		let rec walkNodes nodes res = 
			match nodes with
				| [] -> res
				| snode::rem -> 
					(
						match snode with
							| Leaf(n) -> walkNodes rem (res@[n])
							| Node(n,children) -> 
								let res' = walkNodes children [] in
								walkNodes rem (res@(n::res'))
					)
		in
		walkNodes inputs []
end			
class solutionGenerator (testDriver:fundec) (initializePointers:bool) = object(this)
	
	val mutable unassignedPointers = []
	
	method private mayTakeAddrOf (lh, lo : lhost * offset) = 
		not(Utils.isBitfield lo)
		
	method private getPotentialPointerTargets (plval:lval) (t:typ) (sol:candidateSolution) : ((baseNode * int) list) = 
 		let host = typeSig t in
		let hostTarget = 
			match (unrollType t) with
				| TPtr(t',_) -> typeSig t'
				| _ -> 
					Log.error (Printf.sprintf "%s is not a pointer type\r\n" (Pretty.sprint 255 (Cil.d_type () (unrollType t))))
		in
		List.fold_left(
			fun res node -> 
				if not(Utils.compareLval node.cilLval plval) then (
					let target = typeSig (typeOfLval node.cilLval) in
					if (host = target) then (
						((node,0)::res) 
					) else if (hostTarget = target) then (
						if (this#mayTakeAddrOf node.cilLval) then
							((node,1)::res)
						else
							res
					) else
						res
				) else
					res
		)[](sol#getRevInputList())
		
	method private isPointerTargetNull (l:lval) (sol:candidateSolution) = 
		let nodeOpt = sol#tryFindNodeFromLvalName l in
		match nodeOpt with
			| Some(n) ->
				(
					match n.node with
						| PointerNode(pn) -> (n.bid, pn.pointToNull)
						| _ -> Log.error (Printf.sprintf "%s is not a pointer node\n" (Pretty.sprint 255 (Cil.d_lval()l)))
				) 
			| _ -> Log.error (Printf.sprintf "Failed to find node for %s\n" (Pretty.sprint 255 (Cil.d_lval()l)))
	
	method private clearUnassignedPointerList (sol:candidateSolution) = 
		List.iter(
			fun node -> 
				match node.node with
					| PointerNode(n) -> 
						(
							let targets = this#getPotentialPointerTargets node.cilLval (typeOfLval node.cilLval) sol in
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
									let _id,_isNull = this#isPointerTargetNull targetNode.cilLval sol in
									n.pointToNull <- _isNull;
									n.targetNodeId <- _id;
								)
							)
						)
					| _ -> Log.error "Internal AUSTIN error:clearUnassignedPointerList contains non pointer node\n"
		)unassignedPointers;
		unassignedPointers <- []
			
	method private mkPointerToArrayUpdate (l:lval) (arrayType:typ) (arrayLength:int) (sol:candidateSolution) (ignorePrecon:bool) =
		let rec mkArrayItems cnt res = 
			if cnt >= arrayLength then (
				res
			) else (
				mkArrayItems (cnt + 1) (res@(this#mkUpdatedBaseNodeList (Mem(BinOp(IndexPI, (Lval(l)), (integer cnt), arrayType)), NoOffset) arrayType sol ignorePrecon))
			)
		in
		mkArrayItems 0 []
	
	method private mkArrayUpdate (l:lval) (arrayType:typ) (arrayLength:int) (sol:candidateSolution) (ignorePrecon:bool) =
		let rec mkArrayItems cnt res = 
			if cnt >= arrayLength then (
				res
			) else (
				let l' = addOffsetLval (Index((integer cnt), NoOffset)) l in
				mkArrayItems (cnt + 1) (res@(this#mkUpdatedBaseNodeList l' arrayType sol ignorePrecon))
			)
		in
		mkArrayItems 0 []
	
	method private mkPointerToArrayNew(l:lval) (arrayType:typ) (arrayLength:int) =
		let node = mkPtrNode arrayType (-1) false false true arrayLength l in
		let rec mkArrayItems cnt res = 
			if cnt >= arrayLength then (
				res
			) else (
				mkArrayItems (cnt + 1) (res@(this#mkNewBaseNodeList (Mem(BinOp(IndexPI, (Lval(l)), (integer cnt), arrayType)), NoOffset) arrayType 0))
			)
		in
		(node::(mkArrayItems 0 []))
	
	method private mkArrayNew (l:lval) (arrayType:typ) (arrayLength:int) =
		let rec mkArrayItems cnt res = 
			if cnt >= arrayLength then (
				res
			) else (
				let l' = addOffsetLval (Index((integer cnt), NoOffset)) l in
				mkArrayItems (cnt + 1) (res@(this#mkNewBaseNodeList l' arrayType 0))
			)
		in
		mkArrayItems 0 []
					
	method private mkUpdatedBaseNodeList (l:lval) (t:typ) (sol:candidateSolution) (ignorePrecon:bool) = 
		match t with
			| TInt _ | TFloat _ | TEnum _  -> 
				(
					match sol#tryFindNodeFromLval l with
						| None -> this#mkNewBaseNodeList l t 0
						| Some(n) -> [n]
				)
			| TPtr(pt,_) -> 
				let node = sol#tryFindNodeFromLval l in
				(
					match node with
						| None -> 
							this#mkNewBaseNodeList l t 0
						| Some(n) -> 
							(
								match n.node with
									| PointerNode(pn) -> 
										(
											let handleStdPtrNode () = 
												if pn.isPointerToArray then (
														(n::(this#mkPointerToArrayUpdate n.cilLval pn.targetNodeTyp pn.firstArrayDim sol ignorePrecon))
													) else if not(pn.pointToNull) && pn.targetNodeId = (-1) then (
														(n::(this#mkUpdatedBaseNodeList (Mem(Lval(n.cilLval)), NoOffset) pn.targetNodeTyp sol ignorePrecon))
													) else (
														[n]
													)
											in
											if ignorePrecon then 
												handleStdPtrNode()
											else (
												Log.unimp "Preconditions\n"
											)								
										)
									| _ -> []
							)
				)
			| TArray(at, lengthO, _) -> 
				(
					(this#mkArrayUpdate l at (lenOfArray lengthO) sol ignorePrecon)
				)
			| TFun _ -> Log.error "TFun in solution generator\n"
			| TNamed(ti,_) -> 
				(this#mkUpdatedBaseNodeList l ti.ttype sol ignorePrecon)
			| TComp(ci,_) -> 
				List.fold_left(
					fun res field -> 
						let l' = addOffsetLval (Field(field, NoOffset)) l in
						(res@(this#mkUpdatedBaseNodeList l' field.ftype sol ignorePrecon))
				)[] ci.cfields
			| _ -> (* ignore input *)[]
		
	method private mkNewBaseNodeList (l:lval) (t:typ) (arrayLength:int) = 
		match t with
			| TInt(ikind,_) -> 
				[makeIntNode ikind l]
			| TFloat(fkind,_) -> 
				let value = generateRandomFloatVal () in
				[mkFloatNode value l]
			| TPtr(pt,_) -> 
				(
					if (isFunctionType (unrollType pt)) then []
					else (
						if arrayLength = 0 then (
							(* normal pointer *)
							if initializePointers then (
								if AustinRand.tossCoin() then (
									if AustinRand.tossCoin() then (
										let node = mkPtrNode pt (-1) false false false 0 l in
										(node::(this#mkNewBaseNodeList (Mem(Lval(l)), NoOffset) pt 0))
									) else (
										let node = mkPtrNode pt (0) false false false 0 l in
										unassignedPointers <- (node::unassignedPointers);
										[node]
									)
								) else (
									[mkPtrNode pt (-1) true false false 0 l]
								)
							) else (
								[mkPtrNode pt (-1) true false false 0 l]
							)
						) else (
							(this#mkPointerToArrayNew l pt arrayLength)
						)
					)
				)
			| TArray(at, lengthO, _) ->
				(this#mkArrayNew l at (lenOfArray lengthO))
			| TFun _ -> 
				Log.error "TFun in solution generator\n"
			| TNamed(ti,_) -> 
				(this#mkNewBaseNodeList l ti.ttype arrayLength)
			| TComp(ci,_) -> 
				List.fold_left(
					fun res field -> 
						let l' = addOffsetLval (Field(field, NoOffset)) l in
						(res@(this#mkNewBaseNodeList l' field.ftype 0))
				)[] ci.cfields
			| TEnum(ei,_) -> 
				let len = Int64.of_int (List.length ei.eitems) in
				let value = AustinRand.nextInt64 len in
				[mkIntNode Int64.zero len value l]
			| _ -> (* ignore input *)[]
					
	method prepareTestDriver (fut:fundec) = 
		(* change test driver ids*)
		(* create a mapping from exp to fundecs for all functions in source*)
		let oldIdNewPairs = 
			List.fold_left(
				fun res local -> 
					try
						let vf = List.find(fun formal -> (compare local.vname formal.vname) = 0)fut.sformals in
						((local, vf)::res)
					with
						| Not_found -> res
			)[] testDriver.slocals;
		in
		let vis = new changeVidVisitor oldIdNewPairs in
		ignore(visitCilFunction vis testDriver)
	
	method private correctNodeIds (sol:candidateSolution) = 
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
		
	method generateUpdatedSolution (sol:candidateSolution) (ignorePrecon:bool) = 
		let updated = new candidateSolution in
		updated#setSolutionId (sol#getSolutionId());
		let handleLvalUpdate (l:lval) (t:typ)  = 
			let baseNodes = this#mkUpdatedBaseNodeList l t sol ignorePrecon in
			List.iter(
				fun node -> updated#appendNode node
			)baseNodes
		in
		let rec handleStatement (s : stmt) = 
			match s.skind with
				| Instr(ilist) -> 
					List.iter(
						fun i -> 
							match i with
								| Call(lo, fcall, args, _) -> 
									(
										match lo with
											| Some(l) -> 
												handleLvalUpdate l (typeOfLval l)
											| _ -> ()
									)
								| _ -> ()	
					)ilist
				| Block(b) -> 
					List.iter(
						fun s' -> 
							handleStatement s'
					)b.bstmts
				| _ -> () (* for now ignore the rest *)
		in
		List.iter handleStatement testDriver.sbody.bstmts;
		unassignedPointers <- [];
		this#correctNodeIds(updated);
		updated
		
	method generateNewRandomSolution() = 
		let sol = new candidateSolution in
		let handleLvalNew (l:lval) (t:typ) (arrayLength:int) = 
			let baseNodes = this#mkNewBaseNodeList l t arrayLength in
			List.iter(
				fun node -> sol#appendNode node
			)baseNodes
		in
		let rec handleStatement (s : stmt) = 
			match s.skind with
				| Instr(ilist) -> 
					List.iter(
						fun i -> 
							match i with
								| Call(lo, fcall, args, _) -> 
									(
										match lo with
											| Some(l) -> 
												(
													let functionName = Pretty.sprint 255 (Cil.d_exp()fcall) in
													if startsWith "Austin__generate__Array" functionName then (
														(* second argument is legnth!! *)
														let len = 
															match(isInteger (List.nth args 1)) with
																| None -> 0
																| Some(_int) -> i64_to_int _int
														in
														handleLvalNew l (typeOfLval l) len
													) else (
														handleLvalNew l (typeOfLval l) 0
													)
												)
											| _ -> ()
									)
								| _ -> ()	
					)ilist
				| Block(b) -> 
					List.iter(
						fun s' -> 
							handleStatement s'
					)b.bstmts
				| _ -> () (* for now ignore the rest *)
		in
		List.iter handleStatement testDriver.sbody.bstmts;
		this#clearUnassignedPointerList sol;
		sol
		
end
