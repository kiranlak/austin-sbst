(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil

module Log = LogManager

let arrayInputs : (lval*typ*exp) list ref = ref []
class arrayVisitor = object(this)
	inherit nopCilVisitor
			
	method vfunc (f:fundec) = 
		let tryExtractInt (a:attribute) =
			match a with
				| Attr(_, aplist) ->
					try
						let ap = List.find(fun ap' -> match ap' with AInt(i) -> true | _ -> false)aplist in
						match ap with
							| AInt(i) -> i
							| _ -> 0
					with
						| Not_found -> 0   
		in
		List.iter(
			fun v -> 
				match (unrollType v.vtype) with
					| TPtr(pt,attrs) -> 
						(
							match (Utils.tryGetAttribute "arraylen" attrs) with
								| None -> ()
								| Some(a) -> 
									arrayInputs := ((var v),pt,(integer (tryExtractInt a)))::(!arrayInputs)
						)
					| _ -> ()
		)f.sformals;
		DoChildren
		
	method vinst (i:instr) = 
		match i with
			| Call(lo, fname, args, _) -> 
				(
					if (Pretty.sprint 255 (d_exp()fname)) = "Austin__Assume__Array" then (
						assert((List.length args) = 2);
						let lv,at = 
							match(stripCasts (List.hd (List.tl args))) with
								| Lval(l) -> 
									(
										match (unrollType (typeOfLval l)) with
											| TPtr(pt, _) -> l,pt
											| _ -> l,(typeOfLval l)
									)
								| _ -> 
									Log.error (Printf.sprintf "invalid lval in Austin__Assume__Array:%s\n"
										(Pretty.sprint 255 (Cil.d_exp()(stripCasts (List.hd (List.tl args))))));		
							 
						in
						let dimension = List.hd args in
						arrayInputs := (lv,at,dimension)::(!arrayInputs)
					);
				);
				SkipChildren
			| _ -> DoChildren		
end

let saveArrayInputsToFile () = 
	let outchan = open_out_bin (ConfigFile.find Options.keyArrayFile) in
  Marshal.to_channel outchan (!arrayInputs) [];
  close_out outchan
	
let loadArrayInputsFromFile () = 
	let inchan = open_in_bin (ConfigFile.find Options.keyArrayFile) in
  arrayInputs := (Marshal.from_channel inchan : (lval*typ*exp) list);
  close_in inchan
	
let collectArrayInputsForFunction (fut:fundec) = 
	let vis = new arrayVisitor in
	ignore(visitCilFunction vis fut)
	
let isArrayInput (l:lval) = 
	let matches = List.filter(
		fun (lv',at,dim) ->
			Utils.compareLval l lv'
		)!arrayInputs 
	in
	match matches with
		| [] -> None
		| hd::tl -> Some(hd)

let isArrayField (field:fieldinfo) =
	 let matches = List.filter(
		fun (lv',at,dim) ->
			match lv' with
				| _, Field(field',_) -> 
					if (compare field'.fname field.fname) = 0
						&& (compare field'.fcomp.cname field.fcomp.cname) = 0 then true
					else false
				| _,_ -> false
		)!arrayInputs 
	in
	match matches with
		| [] -> None
		| hd::tl -> Some(hd)
	
let exp_to_int (i:exp) = 
	match (isInteger i) with
		| Some(i64) -> i64_to_int i64
		| None -> 0
		
	