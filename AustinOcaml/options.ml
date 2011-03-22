(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open ConfigFile

let hashtblInitSize = 10000
let maxSymbolicStatements = 100000

let austinOutDir = ref ""
let austinLibDir = ref ""

let mkFileName (name:string) = 
	let exists =
		try
			Sys.is_directory !austinOutDir
		with
			| _ -> false
	in
	if not(exists) && !austinOutDir <> "" then (
		Unix.mkdir !austinOutDir 0o755 (* 0o640 *)
	);
	Filename.concat !austinOutDir name

let keyAustinLibDir = "austinLibDir"
let keyAustinOutDir = "austinOutDir"
let keyBranchTraceName = "branchTrace"

let keySUTpreamble = "sutPreamble"
let keyRenamedMain = "renamedMain"
let keyDrvFundec = "drvFundec"
let keyFutFundec = "futFundec"
let keyBinSolName = "binSolutionDat"
let keyTestCaseFile = "txtTestCases"
let keyInstrumentedSource = "instrumentedSource"
let keyBinInstrumentedSrouce = "binInstrumentedSource"
let keyCfgInfo = "cfgInfo"
let keySymState = "symState"
let keySymPath = "symPath"
let keyBranchIds = "txtBranchIds"
let keyInstrumentLog = "instrLog"
let keyExecLog = "execLog"
let keySUTLog = "sutLog"
let keyLogConfig = "logConfig"

let keyLogToScreen = "logToScreen"
let keyLogToFile = "logToFile"
let keyLogLevel = "logLevel"
let keyLogCsv = "logCsvResults"
let keyLogTestCases = "logTestCases"

let keySeeds = "rndSeeds"

let keyPreconditionFile = "preconFile"
let keyArrayFile = "arrayFile"
let keyBaseLvalsFile = "baseLvals"

let machineDependentPreamble = 
	match Sys.word_size with
		| 32 -> "extra/x86.c"
		| _ -> "extra/x86_64.c"
		
let keyTDGMethod = "tdgSearchMethod"
let keyTDGCriterion = "tdgCriterion"

let keyCompiler = "cc"
let keyCompilerIncl = "compilerIncludes"
let keyCompilerOpts = "compilerOpts"

let keyHillClimberDecimalPlaces = "hillClimberDecimalPlaces"

let addOptionKeysToConfig () = 
	add keySUTpreamble (Filename.concat !austinLibDir machineDependentPreamble);
	add keyRenamedMain "orig_main";
	add keyDrvFundec (mkFileName "drv.dat");
	add keyFutFundec (mkFileName "fut.dat");
	add keyBinSolName (mkFileName "camlSolution.dat");
	add keyTestCaseFile (mkFileName "testCases.c");
	add keyInstrumentedSource (mkFileName "austin_instrumented.c");
	add keyBinInstrumentedSrouce (mkFileName "austin_instrumented.dat");
	add keyCfgInfo (mkFileName "cfginfo.dat");
	add keySymState (mkFileName "symstate.dat");
	add keySymPath (mkFileName "pathCondition.dat");
	add keyBranchIds (mkFileName "branchids.txt");
	add keyInstrumentLog (mkFileName "instrumentation.log");
	add keyExecLog (mkFileName "execution.log"); 
	add keySUTLog (mkFileName "sut.log");
	add keyLogConfig (mkFileName "log.config");
	add keySeeds (mkFileName "randomNumberSeeds.txt");
	add keyBranchTraceName (mkFileName "traceInfo.dat");
	add keyPreconditionFile (mkFileName "precon.dat");
	add keyArrayFile (mkFileName "arrayFile.dat");
	add keyBaseLvalsFile (mkFileName "baseLvals.dat");
	add keyCompiler "gcc";
	add keyCompilerIncl "-I .";
	add keyCompilerOpts "-P -E"	
;;