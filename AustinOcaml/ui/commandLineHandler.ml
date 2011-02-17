(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open ConfigFile

open Instrument
open Execute

module Log = LogManager

exception ConfigFileNotFound of string

let findWildCardSources (name:string) (recursive:bool) = 
	let extFilter = if (endsWith ".c" name) then ".c" else ".i" in
	let cwd = Sys.getcwd () in
	let files = Array.to_list (Sys.readdir cwd) in
	let rec searchFiles (filelist:string list) res = 
		match filelist with
			| [] -> res
			| f::rem -> 
				if (Sys.is_directory f) then (
					if recursive then (
						searchFiles ((Array.to_list (Sys.readdir f)) @ rem) res
					) else (
						searchFiles rem res
					)
				) else (
					if endsWith extFilter f then (
						searchFiles rem (f::res)
					) else
						searchFiles rem res
				)
	in
	searchFiles files []
		
let main () = 
	let instrument = ref false in
	let configName = ref "" in
	let keepOps = ref false in
  let argspec = 
		[ 
			("", Arg.Unit(fun() -> ()), "Global Options:")
		; ("-conf", Arg.String(fun s -> configName:=s), "<path to configuration file>")
		;	("", Arg.Unit(fun() -> ()), "Mandatory Instrumentation Parameters:")
		;	("-i", Arg.Set instrument, "instrument source files")
		; ("-fut", Arg.String(fun s -> insOptFutName:=s), "<name of function under test>")
		;	("", Arg.Unit(fun() -> ()), "Instrumentation Options:")
		; ("-ir", Arg.Unit(fun() -> instrument:=true;insOptRecursive:=true), "\tinstrument source files, but look for files recursively - only works for *.c or *.i")    
		; ("-pp", Arg.Set insOptPPFiles, "preprocess any .c files")
		; ("", Arg.Unit(fun() -> ()), "Mandatory Execution Parameters:")
		; ("-sut", Arg.String(fun s -> execOptsSutPath:=s), "<path to sut.exe>")
		; ("", Arg.Unit(fun() -> ()), "Execution Options:")
		; ("-tid", Arg.Int(fun i -> execOptsTargetId:=i), "set target branch id (node id in Cil CFG)")
		; ("-tindx", Arg.Int(fun i -> execOptsTargetIndex:=i), "set target branch index")
		; ("-maxEvals", Arg.Int(fun i -> execOptsMaxEvals:=i), "set maximum number of fitness evaluations to use")
		; ("", Arg.Unit(fun() -> ()), "Other Options:")
		; ("-keep", Arg.Set keepOps, "keep logical operators")
    ]
	in
	let sources : string list ref = ref [] in
	Arg.parse argspec (
		fun item -> 
			if (endsWith ".c" item) || (endsWith ".i" item) then (
				if startsWith "*." item then
					sources := ((findWildCardSources item !insOptRecursive) @ !sources)
				else
					sources := (item::!sources);
			)
	) "Usage: austin [options] source-files";
	
	if !configName = "" then (
		try
			configName := Sys.getenv "AustinINP"
		with
			| Not_found -> 
				raise (ConfigFileNotFound("could not find environment variable AustinINP and no config file supplied from command line"))
	);
	
	parse !configName;
	
	Options.austinOutDir := find "austinOut";
	Options.austinLibDir := find "austinLib";
	
	Options.addOptionKeysToConfig ();
		
	Log.setupLogLevels();
	
	if not(!instrument) && ((List.length !sources) > 0) && (!execOptsSutPath = "") then
		instrument := true;
		
	if !instrument then (
		Log.setLogChannel (find Options.keyInstrumentLog);
		if (List.length !sources) = 0 then
			Log.error "Did not find any source files\n";
		if !insOptFutName = "" then 
			Log.error "Did not find a function to test\n";
		mainInstrument !sources;
		Log.log (Printf.sprintf "The instrumented file %s is ready to be compiled\n" (find Options.keyInstrumentedSource))
	) else (
		Log.setLogChannel (find Options.keyExecLog);
		if !execOptsSutPath = "" then (
			Log.error "Did not find path to sut\n"
		);
		Cil.initCIL();		
		mainExecute()
	);
	Log.close()	
;;
main()	