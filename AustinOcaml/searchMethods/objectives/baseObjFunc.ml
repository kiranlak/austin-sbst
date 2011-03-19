open Solution

class virtual baseObjFunc = object(this)
	
	method virtual initialize : string list -> int list -> unit
	method virtual evaluate : candidateSolution -> int -> unit
	method virtual compare : candidateSolution -> candidateSolution -> int
end