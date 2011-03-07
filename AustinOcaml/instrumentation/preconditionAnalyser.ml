(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil

module Log = LogManager

let precons = ref []
let strFUT = ref ""

class preconVisitor = object(this)
	inherit nopCilVisitor

	method vfunc (f:fundec) = 
		if (compare f.svar.vname !strFUT) <> 0 then 
			SkipChildren
		else
			DoChildren
				
	method vinst (i:instr) = 
		match i with
			| Call(lo, fname, args, _) -> 
				(
					if (Pretty.sprint 255 (d_exp()fname)) = "Austin__Assume" then (
						let toadd = 
							List.fold_left(
								fun res arg ->
									match arg with
										| BinOp _ -> 
											( 
												(arg::res)
											)
										| _ -> 
											(
												Log.warn "Precondition argument does not appear to be of type BinOp, ignoring it!";
												res
											)
							) [] (List.tl args)
						in
						precons := List.rev_append toadd !precons
					);
				);
				SkipChildren
			| _ -> DoChildren		
end

let savePreconditionsToFile (outname:string) = 
	let rev : exp list = List.rev !precons in
	let outchan = open_out_bin outname in
  Marshal.to_channel outchan rev [];
  close_out outchan
	
class updateAAProto = object(this)
	inherit nopCilVisitor
	
	method vglob (g:global) = 
		match g with
			| GVar(v,ini,loc) -> 
				if v.vname = "Austin__Assume" then (
					v.vattr <- [];
					v.vtype <- TFun(voidType,Some[("argc",uintType,[])],true,[]);
					SkipChildren
				) else DoChildren
			| _ -> DoChildren
end
let collectPreconditions (source:file) (fut:string) (outname:string) = 
	strFUT := fut;
	let vis = new preconVisitor in
	visitCilFile vis source;
	savePreconditionsToFile outname;
	precons := [];
	(* update any Austin__Assume prototype *)
	let vis' = new updateAAProto in
	visitCilFile vis' source
	