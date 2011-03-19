module Log = LogManager
type branchCovObjVal =
{
	appLevel : int;
	branchDist : float;
}

type objectiveValue = Simple of float | BranchCoverage of branchCovObjVal

let mkBranchCovObjVal (a:int) (bd:float) = 
	BranchCoverage({appLevel=a;branchDist=bd})
	
let compareObjVal (o1:objectiveValue) (o2:objectiveValue) = 
	match o1,o2 with
		| BranchCoverage(b1),BranchCoverage(b2) -> 
			if b1.appLevel < b2.appLevel then (-1)
			else if b1.appLevel > b2.appLevel then 1
			else (
				if b1.branchDist < b2.branchDist then (-1)
				else if b1.branchDist > b2.branchDist then 1
				else 0
			)
		| _,_ -> Log.warn "Trying to compare different types of objective value\n";0

let fitness_to_string (v:objectiveValue) = 
	match v with
		| Simple(f) -> string_of_float f
		| BranchCoverage(bo) -> 
			Printf.sprintf "approach level=%d, branch distance=%.10f" bo.appLevel bo.branchDist