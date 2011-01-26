(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open BaseSearchMethod
open BaseObjFunc
open Solution
open SolutionGenerator

class randomSearch (source:file) (drv:fundec) (fut:fundec) = object(this)
	inherit baseSearchMethod source drv fut as super
	
	val solGenerator = 
		new solutionGenerator drv true
			
	method initialize stringParas intParas = 
		solGenerator#prepareTestDriver fut
		
	method search (objFunc:baseObjFunc) = 
		super#reset();
		let rec doSearch () = 
			if currentEvaluations < maxEvaluations then (
				let sol = solGenerator#generateNewRandomSolution() in
				currentEvaluations <- currentEvaluations + 1;
				let saveNewTestCase = objFunc#evaluate sol currentEvaluations in
				if logTestCases && saveNewTestCase then (
					if sol#isIdeal() then
						addSolutionToArchive "target" sol
					else
						addSolutionToArchive "collateral" sol
				);
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