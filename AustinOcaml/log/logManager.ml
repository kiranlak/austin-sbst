(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open Printf
open Pretty

let verbose = ref true
let debug = ref false
let logToScreen = ref true
let logToFile = ref false

type logChannelType = {mutable oc:out_channel option}
let logChannel = {oc=None}

let saveLogConfigToFile() = 
	let saved = (!verbose,!debug,!logToScreen,!logToFile) in
	let outchan = open_out_bin (ConfigFile.find Options.keyLogConfig) in
	Marshal.to_channel outchan saved [];
	close_out outchan
	
let loadLogConfigFromFile() =
	let fname = (ConfigFile.find Options.keyLogConfig) in
	assert(Sys.file_exists fname);
	let inchan = open_in_bin fname in
  let _v,_d,_s,_f = (Marshal.from_channel inchan : (bool*bool*bool*bool)) in
  close_in inchan;
	verbose := _v;
	debug := _d;
	logToScreen := _s;
	logToFile := _f
	
let setupLogLevels () =
	let level = 
		match (ConfigFile.hasKey Options.keyLogLevel) with
			| None -> "none"
			| Some(key) -> key
	in
	if level = "verbose" then
		verbose := true
	else if level = "debug" then (
		verbose := true;
		debug := true;	
	); 
	(match (ConfigFile.hasKey Options.keyLogToScreen) with
		| Some(key) -> logToScreen := key = "true"
		| _ -> ()
	);
	match (ConfigFile.hasKey Options.keyLogToFile) with
		| Some(key) -> logToFile := key = "true"
		| _ -> ()

let setLogChannel (name : string) =
	if !logToFile then (
		(
			match logChannel.oc with
				| Some(oc) -> close_out oc
				| _ -> ()
		);
		logChannel.oc <- Some((*open_out_gen [Open_creat;Open_append;Open_text] 0o755 name*) open_out name)
	)
	
let setLogChannelOpt (id:int) = 
	if id = 0 then
		setLogChannel (ConfigFile.find Options.keyInstrumentLog)
	else if id = 1 then
		setLogChannel (ConfigFile.find Options.keyExecLog)
	else
		setLogChannel (ConfigFile.find Options.keySUTLog)

(**Filename stuff *)
let getUniqueFileName (dir:string) (base:string) (ext:string) = 
	let files = List.filter(fun f -> endsWith ext f)(Array.to_list (Sys.readdir dir)) in
	let rgex = Str.regexp "_" in
	let version = List.fold_left(
		fun cnt f -> 
			let basename = (Str.split rgex f) in
			if (List.length basename) = 0 then
				cnt
			else if (compare base (List.hd basename)) = 0 then
				cnt + 1
			else
				cnt
		)1 files
	in
	Filename.concat dir (base^"_"^(string_of_int version)^ext)
	
(**End *)
			
let close () = 
	match logChannel.oc with
		| Some(oc) -> close_out_noerr oc; logChannel.oc <- None
		| _ -> ()
		
let s () = 
	close ();
	raise Exit

let log (msg:string) = 
  if !verbose then (
		(
			match logChannel.oc with
				| Some(oc) -> 
					Printf.fprintf oc "%s%!" msg
				| _ -> ()
		);
		if !logToScreen then (
			Printf.printf "%s%!" msg
		)
	)

let vassert (msg:string) = 
	(
		match logChannel.oc with
			| Some(oc) -> 
				Printf.fprintf oc "assert: %s%!" msg
			| _ -> ()
	);
	if !logToScreen then (
		Printf.printf "assert: %s%!" msg
	)
	
let warn (msg:string) = 
  if !verbose then (
		(
			match logChannel.oc with
				| Some(oc) -> 
					Printf.fprintf oc "warn: %s%!" msg
				| _ -> ()
		);
		if !logToScreen then (
			Printf.printf "warn: %s%!" msg
		)
	)

let unimp (msg:string) = 
  if !verbose then (
		(
			match logChannel.oc with
				| Some(oc) -> 
					Printf.fprintf oc "unimp: %s%!" msg
				| _ -> ()
		);
		if !logToScreen then (
			(*sendMsgToScreen ("unimp: "^msg);*)
			Printf.printf "unimp: %s%!" msg
		)
	);
	s()
		
let error (msg:string) = 
  if !verbose then (
		(
			match logChannel.oc with
				| Some(oc) -> 
					Printf.fprintf oc "error: %s%!" msg
				| _ -> ()
		);
		if !logToScreen then (
			(*sendMsgToScreen ("error: "^msg);*)
			Printf.printf "error: %s%!" msg
		)
	);
	s ()
		
let debug (msg:string) = 
  if !debug then (
		(
			match logChannel.oc with
				| Some(oc) -> 
					Printf.fprintf oc "debug: %s%!" msg
				| _ -> ()
		);
		if !logToScreen then (
			(*sendMsgToScreen ("debug: "^msg);*)
			Printf.printf "debug: %s%!" msg
		)
	)
	
;;
Callback.register "setLogChannel" setLogChannelOpt;;
Callback.register "closeLogChannel" close;;