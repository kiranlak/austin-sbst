(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open BaseSearchMethod
open BaseObjFunc
open Solution
open SolutionGenerator

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
		new solutionGenerator drv true
			
	val mutable init = true
	val mutable targetId = 0
	val mutable targetIndx = 0
	
	val mutable direction = -1;
  val mutable lastDirection = -1;
  val mutable index = 0;
  val mutable lastIndex = 0;
  val mutable patternMoves = 0;
	
	val mutable currentSolution = new candidateSolution
	val mutable bestSolution = new candidateSolution
	
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
		if full then (
			init <- true;
			numericNodeIndeces <- [];
		)
	
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
	
	method search (objFunc:baseObjFunc) = 
		super#reset();
		this#restart true;
		currentSolution <- solGenerator#generateNewRandomSolution();
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
						if objFunc#compare currentSolution bestSolution < 0 then (
							bestSolution#init(currentSolution);
							this#makePatternMove()
						) else (
							if this#requiresRestart() then (
								Log.log "Random restart\n";
								this#restart true;
								currentSolution <- solGenerator#generateNewRandomSolution();
								this#makeNumTypeNodeList();
							) else (
								currentSolution#init(bestSolution);
								this#exploreNeighbourhood()
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