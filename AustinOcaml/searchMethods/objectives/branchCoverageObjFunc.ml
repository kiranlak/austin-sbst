open Options
open Cfginfo
open BaseObjFunc
open BaseObjValue
open Solution

open Unix

module Log = LogManager

type branchNode = int*int*int

let getFid (fid,_,_) = fid
let getSid (_,sid,_) = sid
let getIndx(_,_,indx) = indx

type branchTraceNode = 
{
	node : branchNode;
	isCritical : bool;
	approachLevel : int;
	branchDistances : float list;
	criticalEdges : int list;
}

module IntMap = Map.Make (struct
                              type t = branchNode
                              let compare (fid1,sid1,indx1) (fid2,sid2,indx2) = 
																let fid = compare fid1 fid2 in
																if fid = 0 then (
																	let sid = compare sid1 sid2 in
																	if sid = 0 then (
																		compare indx1 indx2
																	) else sid
																) else fid
                            end)
exception Not_forked
class branchCoverageObjFunc (pathToSut:string) = object(this)
	inherit baseObjFunc as super
	
	val logTestCases = 
		match (ConfigFile.hasKey Options.keyLogTestCases) with
			| None -> false
			| Some(status) -> status = "true"
			
	val mutable logSerendipitousCoverage : bool = true
	val mutable coveredNewBranches : bool = false
	
	val mutable targetStmtId : int = 0
	val mutable targetIndexId : int = 0
	
	val mutable targetAppLevel : int = 0
	val mutable targetDependent : PS.t = PS.empty
	
	val mutable revbranchTrace : branchTraceNode list = []
	val mutable coverageInfo : (int*int) IntMap.t = IntMap.empty
	
	val optimalFitness = mkBranchCovObjVal 0 0.0
	val worstFitness = mkBranchCovObjVal max_int max_float
	
	val mutable sutException = false
			
	method initialize (stringArgs:string list) (initArgs:int list) = 
		assert((List.length initArgs) = 2);
		targetStmtId <- (List.hd initArgs);
		targetIndexId <- (List.nth initArgs 1);
		let cnt, dependent, _ = getDependentNodesAndEdges targetStmtId in
		targetAppLevel <- cnt;
		targetDependent <- dependent
		
	method writeCoverageInfoToFile (futid:int) (allTargets:(int*int)list) (filename:string) = 
		let oc = open_out_gen [Open_creat;Open_append;Open_text] 0o755 filename in
		output_string oc "nodeid,index,covered,fitnessEvals,numExecuted\n";
		let rec searchIndices (sid:int) (current:int) (total:int) res = 
			if current >= total then
				res
			else (
				let cov,evals,exec = 
					try
						let (evals,cnt) = IntMap.find (futid,sid,current) coverageInfo in
						(1,evals,cnt)
					with
						| Not_found -> (0,(-1),0)
				in
				searchIndices sid (current + 1) total ((current,cov,evals,exec)::res)
			)
		in
		List.iter(
			fun (sid,indices) -> 
				List.iter(
					fun (indx,cov,evals,exec) -> 
						output_string oc (Printf.sprintf "%d,%d,%d,%d,%d\n" sid indx cov evals exec)
				)(searchIndices sid 0 indices [])
		)allTargets;
		close_out oc
		
	method getCoveredBranchCount (tfid:int) (tid:int) (tindx:int) = 
		IntMap.fold(
			fun (fid,sid,indx) (fevals,exec) (tcnt,cnt) ->
				let tcnt' = tcnt + 1 in
				if tid <> (-1) && tindx <> (-1) then (
					(* we have a target stmt and target branch *)
					if tid = sid && tindx = indx then 
						(tcnt',cnt + 1)
					else
						(tcnt',cnt)
				) else if tid <> (-1) && tindx = (-1) then (
					(* we have a target stmt and all branches of that stmt *)
					if tid = sid then 
						(tcnt',cnt + 1)
					else
						(tcnt',cnt)
				)	else if tfid = (-1) && tid <> (-1) then (
					(* we have no target stmt but target branches, e.g. all true *)
					if tindx = indx then 
						(tcnt',cnt + 1)
					else
						(tcnt',cnt)
				) else if tfid <> (-1) && tid <> (-1) then (
					(* we have target branches in a particular function *)
					if tfid = fid && tindx = indx then 
						(tcnt',cnt + 1)
					else
						(tcnt',cnt)
				) else (
					if tfid = fid then
						(tcnt',cnt + 1)
					else
						(tcnt', cnt) 
				)		 
		)coverageInfo (0,0)
	
	method hasTargetBeenCovered (fid:int) (tid:int) (indx:int) = 
		IntMap.mem (fid,tid,indx) coverageInfo
		
	method private normalizeBranchDistance (dist:float) = 
		1.0 -. (1.001 ** (-.dist))
		
	method private updateTraceAndCoverageInfo (currentEvaluations:int) = 
		let traceName = ConfigFile.find Options.keyBranchTraceName in
		let covered = ref false in
		revbranchTrace <- [];
		if not(Sys.file_exists traceName) then (
			Log.log (Printf.sprintf "trace %s doesn't exist\n" 
				traceName);
			false
		) else (
			let ic = open_in (ConfigFile.find Options.keyBranchTraceName) in
			(
				try
			    while true do
			      let line = input_line ic in
			      let items = List.filter(fun i -> i <> "")(Str.split (Str.regexp_string ",") line) in
						if (List.length items < 4) then (
							(* trace IO operation must have been interrupted by alarm, so ignore this and further lines*)
							raise End_of_file
						);
						let fid = int_of_string (List.nth items 0) in
						let sid = int_of_string (List.nth items 1) in
						let indx = int_of_string (List.nth items 2) in
						let dist = ref [] in
						for cnt = 3 to ((List.length items) - 1) do
							dist := ((float_of_string (List.nth items cnt))::!dist)
						done;
						let node = (fid,sid,indx) in
						let critical, appLevel, edges = 
							if sid = targetStmtId then
								true,0,[]
							else
								computeWegenerApproachLevel targetAppLevel targetDependent sid
						in
						let btracenode = 
							if sid = targetStmtId && indx = targetIndexId then (
								covered := true;
								{node=node;isCritical=critical;approachLevel=appLevel;branchDistances=[0.0];criticalEdges=edges}
							) else
								{node=node;isCritical=critical;approachLevel=appLevel;branchDistances=(!dist);criticalEdges=edges}
						in
						revbranchTrace <- (btracenode::revbranchTrace);
						(
							try
								let fevals,cnt = IntMap.find node coverageInfo in
								coverageInfo <- IntMap.add node (fevals,(cnt + 1)) coverageInfo
							with
								| Not_found -> 
									(
										coveredNewBranches <- true;
										coverageInfo <- IntMap.add node (currentEvaluations,1) coverageInfo 
									)
						);
			    done
			  with End_of_file -> ()
			);
			close_in ic;
			!covered
		)
		
	method private computeFitness (currentEvaluations:int) = 
		if targetStmtId > 0 then (
			let covered = this#updateTraceAndCoverageInfo currentEvaluations in
			if covered then (
				if sutException then
					Log.warn "Covered target, but also had SUT exception\n";
				(optimalFitness, true)
			) else (
				let getMinDistance (n:branchTraceNode) = 
					let distances = List.sort(
						fun d1 d2 -> compare d1 d2)n.branchDistances
					in
					List.hd distances
				in
				let rec searchTrace (nodes:branchTraceNode list) = 
					match nodes with
						| [] ->
							if sutException || not(covered) then
								(worstFitness,false)
							else
								(optimalFitness,true)
						| n::rem -> 
							if (n.isCritical) && (not(List.exists(fun i -> (getIndx n.node) = i)n.criticalEdges)) then (
								Log.debug (
									Printf.sprintf "branch node %d index %d is last critical branching node, applevel=%d\n" 
									(getSid n.node) (getIndx n.node) n.approachLevel);
								let fval = mkBranchCovObjVal n.approachLevel (getMinDistance n) in
								if (compareObjVal fval optimalFitness) <= 0 then 
									(optimalFitness, true)
								else
									(fval, false)
							) else
								searchTrace rem
				in
				searchTrace revbranchTrace
			)
		) else (
			(optimalFitness,true)
		) 
	method private executeSUT () = 
		Log.log "Executing SUT...\n";
		let pid = fork () in
		if pid = 0 then (
			let args = Array.make 4 "" in
			Array.set args 0 (Options.keyAustinLibDir);
			Array.set args 1 (!austinLibDir);
			Array.set args 2 (Options.keyAustinOutDir);
			Array.set args 3 (!austinOutDir);
			execv pathToSut args	
		) else if pid < 0 then (
			raise Not_forked
		) else (
			let (_,status) = waitpid [] pid in
			match status with
				| WEXITED(code) -> 
					Log.log (Printf.sprintf "Done SUT (exit code = %d)\n" code);
					if code = 255 then (
						Log.warn "Precondition violation\n";
						sutException <- true;
						true
					) else if code = 254 then (
						Log.warn "Initialization condition violation\n";
						sutException <- true;
						true
					) else if code = 0 then (
						(* OK *)
						sutException <- false;
						false
					) else (
						(* give penalty *)
						sutException <- true;
						false
					)
				| WSIGNALED(signal) | WSTOPPED(signal) -> 
					(
						sutException <- true;
						if signal == Sys.sigalrm then (
							Log.warn "SUT timeout signal\n"
						) else if signal == Sys.sigabrt then (
							Log.warn "SUT abort signal\n"
						) else if signal == Sys.sigsegv then (
							Log.warn (Printf.sprintf "SUT segfault (%d)\n" signal)
						) else (
							Log.warn (Printf.sprintf 
										"Signal handling in branch objective function:%d\n" signal);
						);
						false
					)
		)
		
	method private removeTraceFiles () = 
		let fnames = 
			[ConfigFile.find Options.keyBranchTraceName;ConfigFile.find Options.keySymPath]
		in
		List.iter(
			fun f -> 
				if Sys.file_exists f then (
					Sys.remove f
				)
		)fnames
		
	method evaluate (sol:candidateSolution) (currentEvaluations:int) = 
		this#removeTraceFiles();
		saveCandidateSolutionToFile sol;
		let skipFitness = this#executeSUT () in
		if skipFitness then (
			sol#setFitness worstFitness false
		) else (
			coveredNewBranches <- false;
			let fitness,isIdeal = this#computeFitness currentEvaluations in
			sol#setFitness fitness isIdeal;
			(*sol#print();*)
			if logTestCases && coveredNewBranches then (
				if isIdeal then
					addSolutionToArchive ("target:"^(string_of_int targetStmtId)^","^(string_of_int targetIndexId)) sol
				else
					addSolutionToArchive ("collateral during:"^(string_of_int targetStmtId)^","^(string_of_int targetIndexId)) sol
			)
		)
		
	method compare (s1:candidateSolution) (s2:candidateSolution) = 
		compareObjVal (s1#getFitness()) (s2#getFitness())
end