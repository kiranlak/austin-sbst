(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open Cfginfo
open Utils
open ConfigFile
open BaseSearchMethod
open RandomSearch
open SymbolicHillClimbSearch
open HillClimbSearch
open BaseObjFunc
open BranchCoverageObjFunc
open SolutionGenerator
open Preconditions
open ArrayInputs

module Log = LogManager

let execOptsSutPath = ref ""
let execOptsTargetId = ref (-1)
let execOptsTargetIndex = ref (-1)
let execOptsMaxEvals = ref 100000

let execOptIgnoreCollateral = ref false

let getSearchMethod (source:file) (drv:fundec) (fut:fundec) (search:string) = 
	if search = "random" then
		((new randomSearch source drv fut) :> baseSearchMethod)
	else if search = "chc" then
		((new symbolicHillClimbSearch source drv fut) :> baseSearchMethod)
	else if search = "hc" then
		((new hillClimbSearch source drv fut) :> baseSearchMethod)
	else
		Log.error "Invalid search algorithm\n"

class branchCoverageGenerator (source:file) (drv:fundec) (fut:fundec) (search:string) = object(this)
	
	val searchMethod : baseSearchMethod = (getSearchMethod source drv fut search)
	val objFunc = new branchCoverageObjFunc !execOptsSutPath
	
	val mutable totalUsed = Int64.zero
	val mutable totalSaved = 0
	val mutable failedOnce = false
	
	method private iterateOverIndices (sid:int) (currentIndx:int) (total:int) (saved:int)  = 
		if currentIndx < total then (
			let targetIndexCovered = 
				if not(!execOptIgnoreCollateral) then
					objFunc#hasTargetBeenCovered fut.svar.vid sid currentIndx
				else
					false 
			in
			if not(targetIndexCovered) &&
				(!execOptsTargetIndex = (-1) || (currentIndx = !execOptsTargetIndex)) then (
				objFunc#initialize [] [sid;currentIndx];
				searchMethod#initialize [] [sid;currentIndx];
				searchMethod#setMaxEvaluations (saved + !execOptsMaxEvals);
				Log.log (Printf.sprintf "Attempting branch, stmtid=%d, index=%d\n" sid currentIndx);
				let success = searchMethod#search (objFunc :> baseObjFunc) in
				if not(success) then
					failedOnce <- true;
				let used = searchMethod#getUsedEvaluations() in
				let saved' = 0(*!execOptsMaxEvals + saved - used*) in 
				totalUsed <- (Int64.add totalUsed (Int64.of_int used));
				this#iterateOverIndices sid (currentIndx + 1) total saved'
			) else (
				if targetIndexCovered then (
					Log.log (Printf.sprintf "Skipping covered branch, stmtid=%d, index=%d\n" sid currentIndx);
				);
				this#iterateOverIndices sid (currentIndx + 1) total saved
			)
		) else (
			totalSaved <- totalSaved + saved
		)
	method private iterateOverTargets (targets:(int*int)list) = 
		match targets with
			| [] -> ()
			| (sid,cnt)::rem -> 
				if !execOptsTargetId = (-1) then (
					this#iterateOverIndices sid 0 cnt 0;
					this#iterateOverTargets rem
				) else if !execOptsTargetId <> (-1) then (
					if !execOptsTargetId = sid then (
						this#iterateOverIndices sid 0 cnt 0
					) else
						this#iterateOverTargets rem
				) else () 
						
	method private logResultsToCsvFile (branchInfo:(int*int)list) =
		match (ConfigFile.hasKey Options.keyLogCsv) with
			| None -> ()
			| Some(status) -> (
					if status = "true" then (
						let resultsFile = Log.getUniqueFileName !Options.austinOutDir "csvBranchCoverage" ".csv" in
						objFunc#writeCoverageInfoToFile fut.svar.vid branchInfo resultsFile;
					)
				)
		
	method private printResultToScreen (branchInfo:(int*int)list) (totalBranchCount:int) (totalFutCount:int) = 
		let totalCovered, futCovered = (objFunc#getCoveredBranchCount fut.svar.vid (!execOptsTargetId) (!execOptsTargetIndex)) in
		Log.log (Printf.sprintf "Covered %d out of %d total branches\n" totalCovered totalBranchCount);
		match (!execOptsTargetId,!execOptsTargetIndex) with
			| (-1),(-1) -> 	
				Log.log (Printf.sprintf "Covered %d out of %d fut branches\n" futCovered totalFutCount)
			| (-1), _ -> 
				let targets = 
					List.fold_left(
						fun res (id,cnt) -> 
							if !execOptsTargetIndex > cnt then res
							else (
								res + 1
						  )
					) 0 branchInfo
				in
				Log.log (Printf.sprintf "Covered %d out of %d target branches from fut\n" futCovered targets)
			|  _, (-1) -> 
				let targets = 
					List.fold_left(
						fun res (id,cnt) -> if id = !execOptsTargetId then cnt else res
					) 0 branchInfo
				in
				Log.log (Printf.sprintf "Covered %d out of %d target branches from fut\n" futCovered targets)
			| _,_ ->
				if (objFunc#hasTargetBeenCovered fut.svar.vid !execOptsTargetId !execOptsTargetIndex) then
					Log.log (Printf.sprintf "Covered target %d,%d\n" !execOptsTargetId !execOptsTargetIndex)
				else
					Log.log (Printf.sprintf "Failed to cover target %d,%d\n" !execOptsTargetId !execOptsTargetIndex)
					
	method start () = 
		loadControlDependencies (ConfigFile.find Options.keyCfgInfo);
		let totalBranchCount = countFileBranches source in
		let totalFutCount, branchInfo = countFundecBranches fut in
		this#iterateOverTargets branchInfo;
		this#logResultsToCsvFile branchInfo;
		(****)
		this#printResultToScreen branchInfo totalBranchCount totalFutCount
end

let createTestCasesFromArchive (testdrv:fundec) (fut:fundec) = 
	ignore(List.fold_left(
		fun id (comment,sol) -> 
			ignore(TestCaseWriter.saveCandidateSolution id sol comment testdrv fut);
			(id + 1)
	) 1 (!Solution.solutionArchive))
	
let mainExecute () = 	
	let criterion = ConfigFile.find Options.keyTDGCriterion in
	let search = ConfigFile.find Options.keyTDGMethod in
	let source = unmarshalSource (ConfigFile.find Options.keyBinInstrumentedSrouce) in
	let drv = loadFundecFromFile (ConfigFile.find Options.keyDrvFundec) in
	let fut = loadFundecFromFile (ConfigFile.find Options.keyFutFundec) in
	
	if criterion = "branch" then (
		let testgen = new branchCoverageGenerator source drv fut search in
		loadBaseLvalsFromFile ();
		loadPreconditionsFromFile();
		loadArrayInputsFromFile ();
		Log.saveLogConfigToFile();
		testgen#start();
		createTestCasesFromArchive drv fut
	)
	