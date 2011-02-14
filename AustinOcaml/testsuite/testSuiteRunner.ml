(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open ConfigFile

open Instrument
open Execute

module Log = LogManager

let arch = ref ""

let instrumentSource (fut:string) (source:string) = 
	Log.setLogChannel (find Options.keyInstrumentLog);
	insOptFutName := fut;
	Log.log (Printf.sprintf "tyring to instrument source %s, fut = %s\n"
		source fut);
	mainInstrument [source];
	Log.close()

let compileInstrumented () = 
	let outdir = !Options.austinOutDir in
	let ins_c_file = Filename.concat outdir "austin_instrumented.c" in
	let ins_o_file = Filename.concat outdir "austin_instrumented.o" in
	let sut_file = Filename.concat outdir "sut.exe" in
	let archFlag = match !arch with "" -> "" | _ -> "-arch "^(!arch)^" " in
	let cmpCommand = "gcc "^archFlag^"-c "^ins_c_file^" -o "^ins_o_file in
	Log.log (Printf.sprintf "executing command: %s\n" cmpCommand);
	if (Sys.command cmpCommand) <> 0 then
		Log.error "could not compile instrumented file\n"
	else (
		let mkCommand = "g++ "^archFlag^" -o "^sut_file^" "^ins_o_file^" -L"^(!Options.austinLibDir)^" -lAustinLib -ldl -lm" in
		Log.log (Printf.sprintf "executing command: %s\n" mkCommand);
		if (Sys.command mkCommand) <> 0 then
			Log.error "could not link instrumented object file\n"
	)
	
let executeSUT () = 
	let outdir = !Options.austinOutDir in
	let sut_file = Filename.concat outdir "sut.exe" in
	Log.setLogChannel (find Options.keyExecLog);
	execOptsSutPath := sut_file;
	mainExecute();
	Log.close()

let loadTests (path:string) = 
	let rec collectFiles (base:string) (dir:string) = 
		let dir' = match base with "" -> dir | _ -> Filename.concat base dir in
		let files = Array.to_list (Sys.readdir dir') in
		List.fold_left(
			fun res fname -> 
				let fullname = Filename.concat dir' fname in
				if (Sys.is_directory fullname) && not (startsWith "." fname) then 
					res @ (collectFiles dir' fname)
				else if (endsWith ".c" fname) then (
					fullname::res
				) else
					res
		)[] files
	in
	collectFiles "" path

let getFileFunctions (fname:string) = 
	let file = Frontc.parse fname () in
	List.fold_left(
		fun res g -> 
			match g with
				| GFun(fdec,_) -> 
					fdec.svar.vname::res
				| _ -> res
	)[] file.globals

let resetEvn() = 
	TraceManager.reset();
	Branchtrace.reset();
	Symbolictrace.reset();
	Preprocessor.reset();
	Testdriver.reset(false);
	SolutionGenerator.reset();
	Solution.reset();
	Cfginfo.reset();
	EquivalenceGraph.reset();
	Symbolic.reset();
	Gc.compact()
		
let run () = 
	let testdir = ref "" in
	let configName = ref "" in
	let argspec = 
		[ 
			("-conf", Arg.String(fun s -> configName:=s), "<path to configuration file>")
		;	("-tests", Arg.String(fun s -> testdir:=s), "<path to test suite directory>")
		; ("-maxEvals", Arg.Int(fun i -> execOptsMaxEvals:=i), "set maximum number of fitness evaluations to use")
		; ("-arch", Arg.String(fun s -> arch := s), "set the arch for compilation of sut.exe")
    ]
	in
	Arg.parse argspec (fun item -> ()) "Usage: runTests [options]";
	if !configName = "" then (
		try
			configName := Sys.getenv "AustinINP"
		with
			| Not_found -> 
				failwith "could not find environment variable AustinINP and no config file supplied from command line"
	);
	
	parse !configName;
	
	let dir = 
		match !testdir with
			| "" -> (
					try
						Sys.getenv "AustinTests"
					with
						| Not_found -> failwith "could not find test suite dir")
			| _ -> !testdir
	in
	
	Options.austinOutDir := find "austinOut";
	Options.austinLibDir := find "austinLib";
	
	Options.addOptionKeysToConfig ();
	
	let testFiles = loadTests dir in
	List.iter(
		fun test -> 
			List.iter(
				fun fut ->
					resetEvn();
					instrumentSource fut test;
					compileInstrumented();
					resetEvn();
					executeSUT();
			)(getFileFunctions test)
	)testFiles;;
run()
