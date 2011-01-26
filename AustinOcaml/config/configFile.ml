(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil

(* config keys *)	
let confKeyTDGMethod = "tdgSearchMethod"
let confKeyTDGCriterion = "tdgCriterion"

let confKeyCompiler = "cc"
let confKeyCompilerIncl = "compilerIncludes"
let confKeyCompilerOpts = "compilerOpts"
let confKeyTargetMutants = "targetMutants"

let confFile : (string, string) Hashtbl.t = Hashtbl.create 50

let reset() = 
	Hashtbl.clear confFile
	
let addDefaults = 
	Hashtbl.add confFile confKeyCompiler "gcc";
	Hashtbl.add confFile confKeyCompilerIncl "-I .";
	Hashtbl.add confFile confKeyCompilerOpts "-P -E";
	Hashtbl.add confFile confKeyTargetMutants "false"
	
exception MissingConfigKey of string

let delim = '='
let regDelim = Str.regexp "="
let comment = "#"

let find (key:string) = 
	try
		Hashtbl.find confFile key
	with
		| Not_found -> raise (MissingConfigKey(key))

let hasKey (key:string) = 
	try
		Some(Hashtbl.find confFile key);
	with
		| Not_found -> None
	 
let add (key:string) (value:string) =
	Hashtbl.replace confFile key value
	
let trim str =
	if str = "" then "" else 
		let search_pos init p next =
	    let rec search i =
	      if p i then raise(Failure "empty") else
		      match str.[i] with
			      | ' ' | '\n' | '\r' | '\t' -> search (next i)
			      | _ -> i
	    in
    	search init
		in   
		let len = String.length str in   
		try
    	let left = search_pos 0 (fun i -> i >= len) (succ)
    	and right = search_pos (len - 1) (fun i -> i < 0) (pred)
   		in
    	String.sub str left (right - left + 1)   
		with 
			| Failure "empty" -> ""

let parseArgumentOption (arg:string) = 
	if String.contains arg delim then (
		let items = List.map(fun i -> trim i)(Str.split regDelim arg) in
		assert((List.length items) = 2);
		((List.nth items 0), (List.nth items 1))
	) else
		("","")
		
let parse (file:string) =
	if Sys.file_exists file then (
		let ic = open_in file in
		(
			try
		    while true do
		      let line = input_line ic in
					if not(startsWith comment line) then (
						if String.contains line delim then (
							let items = List.map(fun i -> trim i)(Str.split regDelim line) in
							assert((List.length items) = 2);
							Hashtbl.replace confFile (List.nth items 0) (List.nth items 1)
						)
					)
		    done
		  with End_of_file -> ()
		);
		close_in ic
	) else 
		failwith (Printf.sprintf "config file: %s not found\n" file);
		