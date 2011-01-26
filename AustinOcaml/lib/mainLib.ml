(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open Options
open Solution

let source = ref dummyFile
let inputNodes = ref []

let initializeOcaml (out:string) (lib:string) = 
	initCIL();
	austinOutDir := out;
	austinLibDir := lib;
	addOptionKeysToConfig ();
	let sol =  (loadCandidateSolutionFromFile ()) in
	inputNodes := sol#getInputList();
	Log.setLogChannelOpt 2
;;
Callback.register "initializeOcaml" initializeOcaml;;