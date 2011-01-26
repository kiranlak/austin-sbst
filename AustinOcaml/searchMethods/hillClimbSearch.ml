(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open BaseSearchMethod
open BaseObjFunc
open Solution
open SolutionGenerator
open Symbolic

module EQ = EquivalenceGraph
module Log = LogManager

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

class hillClimbSearch (source:file) (drv:fundec) (fut:fundec) = object(this)
	inherit baseSearchMethod source drv fut as super
	
	val solGenerator = 
		new solutionGenerator drv false
			
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
		solGenerator#prepareTestDriver fut;
		targetId <- (List.hd intParas);
		targetIndx <- (List.hd (List.tl intParas))
		
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
		symEnterFunctionSimple drv;
		List.iter(
			fun node -> 
				updateStateEx node.cilLval (Some(fut)) true (SymEx(CilExpr(Lval(node.cilLval))))
		)(currentSolution#getRevInputList());
		Symbolic.saveCurrentStateToFile (ConfigFile.find Options.keySymState)
		
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
				let delta = (float dir) *. 0.01 *. (2.0**(float patternMoves)) in
				_fn.fval <- float_of_string (Printf.sprintf "%.2f" (_fn.fval +. delta))
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
		(*Log.log (Printf.sprintf "graph before move:\n%s\n"
			(Pretty.sprint 255 (EQ.printGraph())));*)
		let lvals = ref [] in
		let addr = ref [] in
		
		let findNodeFromLvalName (l:lval) = 
			match (currentSolution#tryFindNodeFromLvalName l) with
				| None -> Log.error (Printf.sprintf "Failed to find %s in input node list\n" (Pretty.sprint 255 (Cil.d_lval () l)));
				|	Some(n) -> n
		in
		let setLvalsToNull (lvals:lval list) =
			 List.iter(
				fun l -> 
					let node = findNodeFromLvalName l in
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
					let n = findNodeFromLvalName l in
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
		let containsAnAddrOf (elements:exp list) =
			if not(List.exists(fun e -> match (stripCasts e) with AddrOf _ -> true | _ -> false)elements) then (
				List.exists (
					fun e -> 
						lvals := [];
						addr := [];
						let vis = new collectLvalFromExprVisitor lvals addr in 
						ignore(visitCilExpr vis e);
						(List.length !addr) <> 0
				) elements
			) else
				true 
		in
		let containsConstant (elements:exp list) =
			List.filter(fun e -> isConstant e)elements
		in
		List.iter(
			fun eqNode -> 
				if (containsAnAddrOf (EQ.EquivalenceNode.elements eqNode.EQ.elements)) then (
					(**TODO: addressOf *)
					Log.unimp "AddrOf in EQ node\n"
				) else (
					let constants = containsConstant (EQ.EquivalenceNode.elements eqNode.EQ.elements) in
					if (List.length constants) > 0 then (
						if not(isZero (List.hd constants)) then 
							Log.unimp "Non-zero constant in EQ node\n";
						EQ.EquivalenceNode.iter(
							fun e ->
								lvals := [];
								addr := [];
								let vis = new collectLvalFromExprVisitor lvals addr in 
								ignore(visitCilExpr vis e);
								setLvalsToNull (!lvals @ !addr);
						)eqNode.EQ.elements
					) else (
						let nodeEdgeCnt = (EQ.IntSet.cardinal eqNode.EQ.edges) in
						if nodeEdgeCnt = 0 ||
							 (EQ.containsZeroNode eqNode) then (
							EQ.EquivalenceNode.iter(
								fun e ->
									lvals := [];
									addr := [];
									let vis = new collectLvalFromExprVisitor lvals addr in 
									ignore(visitCilExpr vis e);
									setLvalsToNull (!lvals @ !addr);
							)eqNode.EQ.elements
						) else (
							let e = EQ.EquivalenceNode.choose eqNode.EQ.elements in
							lvals := [];
							addr := [];
							let vis = new collectLvalFromExprVisitor lvals addr in 
							ignore(visitCilExpr vis e);
							assert((List.length !lvals) > 0);
							let l = List.hd !lvals in
							let node = findNodeFromLvalName l in
							(
								match node.node with
									| PointerNode(pn) -> 
										pn.targetNodeId <- (-1);
										pn.pointToNull <- false;
										pn.takesAddrOf <- false
									| _ -> 
										Log.warn (Printf.sprintf "Was expecting pointer (to assign malloc), but received %s (ignoring)\n" (Pretty.sprint 255 (Cil.d_type() (typeOfLval node.cilLval))))
							);
							EQ.EquivalenceNode.iter(
								fun e ->
									lvals := [];
									addr := [];
									let vis = new collectLvalFromExprVisitor lvals addr in 
									ignore(visitCilExpr vis e);
									setLvalsToTID !lvals node
							)eqNode.EQ.elements
						)
					)
				)
		)!EQ.eqGraph
		
	method private makePointerMove (conj : (int*int*exp)) = 
		(**************************)
		let thrd (_,_,a) = a in
		Log.log "Pointer move...";
		let conjExpr = thrd conj in
		Log.log (Printf.sprintf "\ntrying to solve inv of %s\n" (Pretty.sprint 255 (Cil.d_exp()conjExpr)));
		let lhsExprAlia,rhsExprAlia = (*findPCConjunctAliaExpr conjExpr*) ([],[]) in
		EQ.addExpressionToGraph (Symbolic.tryInvertOp conjExpr) lhsExprAlia rhsExprAlia;
		isPointerMove <- true;
		this#trySolvePointerConstraints();
		currentSolution <- (solGenerator#generateUpdatedSolution currentSolution true);
		Log.log "done\n"
			
	method private doesConstraintRequireSolving (sid,index:int*int) = 
		let criticalEdges = ((targetId,targetIndx)::(Cfginfo.getCriticalEdges targetId)) in
		let exists (sid',index') = sid' = sid && index' = index in
		let notExists (sid',index') = sid' = sid && index' <> index in
		not(List.exists exists criticalEdges) && (List.exists notExists criticalEdges)
	
	method private requiresPointerMove () =
		let pcFilename = (ConfigFile.find Options.keySymPath) in
		assert(Sys.file_exists pcFilename);
		Symbolic.loadPCfromFile pcFilename;
			try
				Some(List.find (
					fun (sid,index,con) ->
						(EQ.expDependsOnMem con) && (this#doesConstraintRequireSolving (sid,index))
				)(List.rev Symbolic.pc.Symbolic.conjuncts))
			with
				| Not_found -> None
	
	method search (objFunc:baseObjFunc) = 
		super#reset();
		this#restart true;
		currentSolution <- solGenerator#generateNewRandomSolution();
		this#initializeSymbolicState();
		this#makeNumTypeNodeList();
		
		let rec doSearch() = 
			if currentEvaluations < maxEvaluations then (
				currentEvaluations <- currentEvaluations + 1;
				let saveNewTestCase = objFunc#evaluate currentSolution currentEvaluations in
				if init then (
					bestSolution#init(currentSolution);
					init <- false;
				);
				if logTestCases && saveNewTestCase then (
					if currentSolution#isIdeal() then
						addSolutionToArchive "target" currentSolution
					else
						addSolutionToArchive "collateral" currentSolution
				);
				if currentSolution#isIdeal() then (
					bestSolution#init(currentSolution);
					true
				) else (
					(
						match (this#requiresPointerMove ()) with
							| Some(conj) -> 
								(
									this#makePointerMove conj;
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
											currentSolution <- solGenerator#generateNewRandomSolution();
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