(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open BaseSearchMethod
open BaseObjFunc
open Solution
open SolutionGenerator
open Symbolic

module EQ = EquivalenceGraph
module Log = LogManager

let precision = 
	match (ConfigFile.hasKey Options.keyHillClimberDecimalPlaces) with
		| None -> 0.01
		| Some(places) -> 
			10.0 ** (-. (float_of_string places))

class containsNonInputLval (hasNonInput:bool ref) (definedLvals:lval list) = object
	inherit nopCilVisitor 
	method vlval (l:lval) = 
		if List.for_all(fun l' -> not(Utils.compareLval l' l))definedLvals then (
			hasNonInput := true;
		);
		SkipChildren
end
class collectLvalFromExprVisitor (lv:lval list ref) (addr:lval list ref) = object(self)
	inherit nopCilVisitor
	
	method vexpr (e:exp) = begin
		match e with
			| Lval (l) -> 
				lv := (l::!lv); SkipChildren
			| AddrOf (l) -> 
				addr := (l::!addr); SkipChildren
			| StartOf (l) -> 
				addr := (l::!addr); SkipChildren
			| _ -> DoChildren	
	end
end

class symbolicHillClimbSearch (source:file) (drv:fundec) (fut:fundec) = object(this)
	inherit baseSearchMethod source drv fut as super
				
	val mutable init = true
	val mutable targetId = 0
	val mutable targetIndx = 0
	
	val mutable direction = -1;
  val mutable lastDirection = -1;
  val mutable index = 0;
  val mutable lastIndex = 0;
  val mutable patternMoves = 0;
	val mutable isPointerMove = false
	
	val mutable currentSolution = new candidateSolution
	val mutable bestSolution = new candidateSolution
	
	val mutable updateNodeList = false
	val mutable numericNodeIndeces = []
	
	method initialize stringParas intParas = 
		targetId <- (List.hd intParas);
		targetIndx <- (List.hd (List.tl intParas));
		initializePointers := false
		
	method private restart (full:bool) = 
		direction <- -1;
		lastDirection <- -1;
		index <- 0;
		lastIndex <- 0;
		patternMoves <- 0;
		isPointerMove <- false;
		updateNodeList <- false;
		if full then (
			init <- true;
			EQ.emptyGraph ();
			numericNodeIndeces <- [];
		)
	
	method private initializeSymbolicState () = 
		Symbolic.reset();
		List.iter(
			fun node -> 
				Symbolic.assign node.cilLval (Lval(node.cilLval));
		)(currentSolution#getRevInputList());
		Symbolic.saveCurrentStateToFile ()
		
	method private makeNumTypeNodeList () = 
		let indx = ref (-1) in
			numericNodeIndeces <- (List.fold_left(
			fun res node -> 
				incr indx;
				match node.node with
					| PointerNode _ -> res
					| _ -> ((!indx)::res)
			) [] (currentSolution#getRevInputList()))
				
	method private makeNumericalMove (isPatternMove : bool) = 
		assert((List.length numericNodeIndeces) > 0);
		let dir = if isPatternMove then lastDirection else direction in
		let indx = if isPatternMove then lastIndex else index in
		assert((List.length numericNodeIndeces) > indx);
		(* if the current var is an integral then do +- 1 else compute a float from gaussian distribution *) 
		let node = 
			currentSolution#getNodeAt (List.nth numericNodeIndeces indx)
		in
		match node.node with
			| IntNode(_in) -> 
				let delta = (float dir) *. 1.0 *. (2.0**(float patternMoves)) in
				let val' = Int64.add _in.ival (Int64.of_float delta) in
				if val' < _in.imin then
					_in.ival <- _in.imin
				else if val' > _in.imax then
					_in.ival <- _in.imax
				else
					_in.ival <- val'
			| FloatNode(_fn) -> 
				let delta = (float dir) *. precision *. (2.0**(float patternMoves)) in
				let val' = round (_fn.fval +. delta) precision in
				if val' < _fn.fmin then
					_fn.fval <- _fn.fmin
				else if val' > _fn.fmax then
					_fn.fval <- _fn.fmax
				else
					_fn.fval <- val'
			| _ ->  Log.error "Wrong node type in numeric move\n"
						
	method requiresRestart () = 
		index >= (List.length numericNodeIndeces) && patternMoves = 0
		
	method private exploreNeighbourhood () = 
		if patternMoves <> 0 then
			this#restart false;
		Log.log "Exploratory move...";
		lastDirection <- direction;
    lastIndex <- index;
    this#makeNumericalMove false;
		if direction < 0 then
			direction <- 1
    else (
			direction <- -1;
      index <- index + 1;
    );
		Log.log "done\n"
		
	method private makePatternMove () = 
		Log.log "Pattern move...";
		patternMoves <- patternMoves + 1;
		this#makeNumericalMove true;
		Log.log "done\n"
	
	method private trySolvePointerConstraints () = 
		(* iterate over all nodes in the EQ and instantiate them*)
		(*Log.debug (Printf.sprintf "graph before move:\n%s\n"
			(Pretty.sprint 255 (EQ.printGraph())));*)
		let lvals = ref [] in
		let addr = ref [] in
		let definedLvals = List.map(fun n -> n.cilLval)(currentSolution#getRevInputList()) in
		
		let getValidLvalsFromNode (n:EQ.EquivalenceNode.t) = 
			lvals := [];
			addr := [];
			let vis = new collectLvalFromExprVisitor lvals addr in
			List.iter(
				fun el -> 
					ignore(visitCilExpr vis el)
			)(EQ.EquivalenceNode.elements n);
			lvals := List.filter(
				fun l -> 
					let hasNonInput = ref false in
					let vis2 = new containsNonInputLval hasNonInput definedLvals in
					ignore(visitCilLval vis2 l);
					not(!hasNonInput)		
			)!lvals;
			addr := List.filter(
				fun l -> 
					let hasNonInput = ref false in
					let vis2 = new containsNonInputLval hasNonInput definedLvals in
					ignore(visitCilLval vis2 l);
					not(!hasNonInput)		
			)!addr;
		in
		
		let findNodeFromLval (l:lval) = 
			match (currentSolution#tryFindNodeFromLval l) with
				| None -> 
					currentSolution#print();
					Log.error (Printf.sprintf "Failed to find %s in input node list\n" (Pretty.sprint 255 (Cil.d_plainlval () l)));
				|	Some(n) -> n
		in
		let setLvalsToNull (lvals:lval list) =
			 List.iter(
				fun l -> 
					let node = findNodeFromLval l in
					match node.node with
						| PointerNode(pn) -> 
							pn.targetNodeId <- (-1);
							pn.pointToNull <- true;
							pn.takesAddrOf <-false;
						| _ -> 
							Log.warn (Printf.sprintf "Was expecting pointer (to set to null), but received %s (ignoring)\n" (Pretty.sprint 255 (Cil.d_type() (typeOfLval node.cilLval))))
			)lvals
		in
		let setLvalsToTID (lvals:lval list) (node:baseNode) =
			 List.iter(
				fun l -> 
					let n = findNodeFromLval l in
					if n.bid <> node.bid then (
						match n.node,node.node with
							| PointerNode(pn),PointerNode(tpn) -> 
								pn.targetNodeId <- node.bid;
								pn.pointToNull <- tpn.pointToNull;
								pn.takesAddrOf <- tpn.takesAddrOf;
							| _,_ -> 
								Log.warn (Printf.sprintf "Was expecting pointer (to assign tid), but received %s (ignoring)\n" (Pretty.sprint 255 (Cil.d_type() (typeOfLval n.cilLval))))
					)
			)lvals
		in
		let containsAnAddrOf (n:EQ.EquivalenceNode.t) =
			getValidLvalsFromNode n;
			(List.length !addr) <> 0
		in
		let containsConstant (elements:exp list) =
			List.filter(fun e -> isConstant e)elements
		in
		List.iter(
			fun eqNode -> 
				if (containsAnAddrOf eqNode.EQ.elements) then (
					(**TODO: addressOf *)
					Log.unimp "AddrOf in EQ node\n"
				) else (
					let constants = containsConstant (EQ.EquivalenceNode.elements eqNode.EQ.elements) in
					if (List.length constants) > 0 then (
						if not(isZero (List.hd constants)) then 
							Log.unimp "Non-zero constant in EQ node\n";
						getValidLvalsFromNode eqNode.EQ.elements;
						setLvalsToNull (!lvals @ !addr)
					) else (
						let nodeEdgeCnt = (EQ.IntSet.cardinal eqNode.EQ.edges) in
						if nodeEdgeCnt = 0 ||
							 (EQ.containsZeroNode eqNode) then (
							getValidLvalsFromNode eqNode.EQ.elements;
							setLvalsToNull (!lvals @ !addr);
						) else (
							getValidLvalsFromNode eqNode.EQ.elements;
							(**)
							(* this can happen if you have a global var G that's initialized, thus not part*)
							(* of input and a constraint T != G *)
							(* assert((List.length !lvals) > 0);*)
							if(List.length !lvals) > 0 then (
								let l = List.hd !lvals in
								let node = findNodeFromLval l in
								(
									match node.node with
										| PointerNode(pn) -> 
											pn.targetNodeId <- (-1);
											pn.pointToNull <- false;
											pn.takesAddrOf <- false
										| _ -> 
											Log.warn (Printf.sprintf "Was expecting pointer (to assign malloc), but received %s (ignoring)\n" (Pretty.sprint 255 (Cil.d_type() (typeOfLval node.cilLval))))
								);
								setLvalsToTID !lvals node
							)
						)
					)
				)
		)!EQ.eqGraph
		
	method private makePointerMove (sconj : stmtConj) = 
		(**************************)
		Log.log "Pointer move...";
		let debug_str = ref "" in
		(**TODO: stricly speaking, each atomicConditions is a || condition, so 
it doesn't make sense to add all to the EQ graph. But since I'm no using the EQ for 
arithmetic inputs this should be ok for now **)
		List.iter(
			fun aliaExprlist -> 
				if List.length aliaExprlist > 0 then (
					let toinvert = Utils.tryInvertOp (List.hd aliaExprlist) in
					if !debug_str <> "" then
						debug_str := (!debug_str)^" || ";
						
					debug_str := (!debug_str)^(Printf.sprintf "(%s" (Pretty.sprint 255 (Cil.d_exp()toinvert)));

					EQ.addExpressionToGraph toinvert;
					
					debug_str := (!debug_str) ^ (List.fold_left(
						fun str' aliaExpr -> 
							EQ.addExpressionToGraph aliaExpr;
							if str' = "" then 
								Printf.sprintf " && %s" (Pretty.sprint 255 (Cil.d_exp()aliaExpr))
							else
								str'^" && "^(Printf.sprintf "%s" (Pretty.sprint 255 (Cil.d_exp()aliaExpr)))
							
					) "" (List.tl aliaExprlist));
					
					debug_str := (!debug_str)^") "
				)
		)(getStmtConditions sconj);
		Log.debug (Printf.sprintf "\n\ntrying to satisfy:%s\n" !debug_str);
		isPointerMove <- true;
		this#trySolvePointerConstraints();
		currentSolution <- (generateUpdatedSolution currentSolution);
		Log.log "done\n"
			
	method private doesConstraintRequireSolving (sid,index:int*int) = 
		let criticalEdges = ((targetId,targetIndx)::(Cfginfo.getCriticalEdges targetId)) in
		let exists (sid',index') = sid' = sid && index' = index in
		let notExists (sid',index') = sid' = sid && index' <> index in
		not(List.exists exists criticalEdges) && (List.exists notExists criticalEdges)
	
	method private requiresPointerMove () =
		Symbolic.loadPathConditionfromFile ();
		(*Symbolic.printPathCondition();*)
		try
			Some(List.find (
				fun (sid,index,atomicList) ->
					List.exists(
						fun conlist ->
							List.exists(
								fun con ->  
									(EQ.expDependsOnMem con) && (this#doesConstraintRequireSolving (sid,index))
							)conlist
					)atomicList
			)(List.rev Symbolic.pc.Symbolic.conjuncts))
		with
			| Not_found -> None
	
	method search (objFunc:baseObjFunc) = 
		super#reset();
		this#restart true;
		currentSolution <- generateNewRandomSolution();
		this#initializeSymbolicState();
		this#makeNumTypeNodeList();
		
		let rec doSearch() = 
			if currentEvaluations < maxEvaluations then (
				currentEvaluations <- currentEvaluations + 1;
				objFunc#evaluate currentSolution currentEvaluations;
				if init then (
					bestSolution#init(currentSolution);
					init <- false;
				);
				if currentSolution#isIdeal() then (
					bestSolution#init(currentSolution);
					true
				) else (
					(
						match (this#requiresPointerMove ()) with
							| Some(conjs) -> 
								(
									this#makePointerMove conjs;
									this#initializeSymbolicState();
									this#makeNumTypeNodeList();
									isPointerMove <- true
								)
							| None -> 
								(
									if objFunc#compare currentSolution bestSolution < 0 then (
										bestSolution#init(currentSolution);
										if not(isPointerMove) then (
											this#makePatternMove()
										) else (
											this#restart false;
											this#exploreNeighbourhood()
										)
									) else (
										if isPointerMove || this#requiresRestart() then (
											Log.log "Random restart\n";
											this#restart true;
											currentSolution <- generateNewRandomSolution();
											this#initializeSymbolicState();
											this#makeNumTypeNodeList();
										) else (
											currentSolution#init(bestSolution);
											if updateNodeList then (
												this#restart false;
												this#makeNumTypeNodeList();
											);
											this#exploreNeighbourhood()
										)
									)
								)
						);
						doSearch()
				)
			) else (
				false
			)
		in
		doSearch()
end