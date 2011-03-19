(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open BaseSearchMethod
open BaseObjFunc
open Solution
open SolutionGenerator

class randomSearch (source:file) (drv:fundec) (fut:fundec) = object(this)
	inherit baseSearchMethod source drv fut as super
			
	method initialize stringParas intParas = 
		initializePointers := true
		
	method search (objFunc:baseObjFunc) = 
		super#reset();
		let rec doSearch () = 
			if currentEvaluations < maxEvaluations then (
				let sol = generateNewRandomSolution() in
				currentEvaluations <- currentEvaluations + 1;
				objFunc#evaluate sol currentEvaluations;
				if sol#isIdeal() then (
					true
				) else (
					doSearch ();
				)
			) else
				false
		in
		doSearch()
end