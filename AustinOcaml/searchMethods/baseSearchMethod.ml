(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open Solution
open BaseObjFunc

class virtual baseSearchMethod (source:file) (drv:fundec) (fut:fundec) = object(this)

	val mutable maxEvaluations : int = 0
	val mutable currentEvaluations : int = 0

	val logTestCases = 
		match (ConfigFile.hasKey Options.keyLogTestCases) with
			| None -> false
			| Some(status) -> status = "true"

	method reset () = 
		currentEvaluations <- 0;
		Solution.reset()
		
	method setMaxEvaluations (maxEvals:int) = 
		maxEvaluations <- maxEvals
	
	method getMaxEvaluations () = 
		maxEvaluations
		
	method getUsedEvaluations () = 
		currentEvaluations
	
	method virtual initialize : string list -> int list -> unit
	method virtual search : baseObjFunc -> bool
	  
end