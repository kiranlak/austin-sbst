(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil

class unsupportedVisitor (found:bool ref) = object
	inherit nopCilVisitor 
	
	method vfunc (f:fundec) = 
		if (startsWith "Austin__" f.svar.vname) then SkipChildren
		else DoChildren
		
	method vinst (i:instr) =
		match i with
			| Call(_,f,_,_) -> 
				(
					match (stripCasts f) with
						| Lval(l) -> 
							(
								match l with
									| Var vi, _ -> 
										if vi.vname = "longjmp" || vi.vname = "setjmp" then (
											found := true;
											SkipChildren
										) else
											DoChildren
									| _ -> DoChildren
							)
						| _ -> DoChildren
				)
				
			| _ -> DoChildren 
end

let hasUnsupportedFeature (source:file) = 
	let found = ref false in
	let vis = new unsupportedVisitor found in
	visitCilFileSameGlobals vis source;
	!found
	