(* Copyright: Kiran Lakhotia, University College London, 2011 *)
let seed = ref (abs (truncate (Unix.time ())))

let init = Random.init !seed

let setRandomSeed (s:int) = 
	seed := s;
	Random.init s

let nextInt () = 
	Random.int (int_of_float ((2.0**30.0) -. 1.0))

let nextFloat () = 
	Random.float max_float

	
let nextInt (upper:int) = 
	Random.int upper

let nextFloat ?(lower=0.0) (upper:float) = 
	let min,max = if lower > upper then upper,lower else lower,upper in
	((Random.float 1.0) *. (max -. min)) +. min
			
let nextInt64 ?(lower=Int64.zero) (upper:int64) = 
	let _fl = Int64.to_float lower in
	let _fu = Int64.to_float upper in
	let min,max = if _fl > _fu then _fu,_fl else _fl,_fu in 
	let r = (nextFloat ~lower:min max) in
	Int64.of_float r

let tossCoin () = 
	Random.bool ()