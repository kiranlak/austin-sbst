(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open Printf
open Pretty
open Utils

module Log = LogManager

let uniqueSymAddressIndex = ref 0
let getNextUniqueSymAddressIndex (size:int) = 
	let id = !uniqueSymAddressIndex in
	uniqueSymAddressIndex := !uniqueSymAddressIndex + size + 1;
	id
	
type symStackAddress =
{
	hostAddress : int;  (* based on Cil.bitsSizeOf type function + uniqueAddressIndex *)
	offsetAddress : int; (* based on Cil.bitsOffset type offset function *)
}
type symExp = Undef | CilExpr of exp
type symContent = StackAddress of symStackAddress | SymEx of symExp
type symLval = 
{
	symAddr : symStackAddress;
	containingFunc : fundec option; (* function where lval is defined. For globals set to None *)
	mutable content : symContent;
	mutable isInput : bool;
}

type pathCondition = {mutable conjuncts : (int*int*exp) list; mutable pathExpression : exp}

type symStackFrameItem = 
{
	mutable state : symLval LvalHashtbl.t
}

let symStackFrameItems : (fundec option * lval option * symStackFrameItem) list ref = ref []
let pc = {conjuncts = [];pathExpression = one}

let getFunctionFromStackFrame ((fo,lo,frame) : (fundec option * lval option * symStackFrameItem)) = 
	fo

let getReturnLvalFromStackFrame ((fo,lo,frame) : (fundec option * lval option * symStackFrameItem)) = 
	lo

let getFrameFromStackFrame ((fo,lo,frame) : (fundec option * lval option * symStackFrameItem)) = 
	frame
	
let clearState () = 
	symStackFrameItems := []

let reset () = 
	uniqueSymAddressIndex := 0;
	symStackFrameItems := [];
	pc.conjuncts <- [];
	pc.pathExpression <- one
	
let saveCurrentStateToFile (fileName:string) = 
	let len = List.length !symStackFrameItems in
	if len > 0 then (
		let outchan = open_out_bin fileName in
		Marshal.to_channel outchan (List.nth !symStackFrameItems (len - 1)) [];
		close_out outchan
	)
	
let loadStateFromFile (fileName:string) = 
	let inchan = open_in_bin fileName in
  let saved = (Marshal.from_channel inchan : (fundec option * lval option * symStackFrameItem)) in
  close_in inchan;
	symStackFrameItems := [saved]

let savePCtoFile (fileName:string) = 
	let outchan = open_out_bin fileName in
  Marshal.to_channel outchan pc [];
  close_out outchan

let loadPCfromFile (fileName:string) =
	let inchan = open_in_bin fileName in
  let saved = (Marshal.from_channel inchan : pathCondition) in
  close_in inchan;
	pc.conjuncts <- saved.conjuncts;
	pc.pathExpression <- saved.pathExpression
	
let tryFindLvalInCurrentStackFrame (l:lval) = 
	if (List.length !symStackFrameItems) > 0 then (
		let current = getFrameFromStackFrame (List.hd !symStackFrameItems) in
		try
			Some(LvalHashtbl.find current.state l)
		with
			| Not_found -> None
	) else
		None
		
let tryFindLvalInStackFrames (l:lval) = 
		
	let rec search (items:(fundec option * lval option * symStackFrameItem) list) = 
		match items with
			| [] -> None
			| (_,_,i)::rem ->  
				try
					Some(LvalHashtbl.find i.state l)
				with
					| Not_found -> search rem
	in
	search !symStackFrameItems
	
let tryFindStackAddress (l:lval) = 
	let symlvO = tryFindLvalInStackFrames l in
	match symlvO with
		| None -> None
		| Some(symlv) -> Some(symlv.symAddr)
	
exception SymStackAddressFound of lval
let tryFindLvalFromStackAddress (addr:symStackAddress) = 
	let rec search (items:(fundec option * lval option * symStackFrameItem) list) =
		match items with
			| [] -> None
			| (_,_,i)::rem -> 
				try
					LvalHashtbl.iter(
						fun lv symlv -> 
							if symlv.symAddr.hostAddress = addr.hostAddress &&
								symlv.symAddr.offsetAddress = addr.offsetAddress then
									raise (SymStackAddressFound(lv))
					)i.state;
					search rem
				with
					| SymStackAddressFound(l) -> Some(l)  
	in
	search !symStackFrameItems
	
let mkNewSymAddressForLval (l:lval) = 
	{hostAddress=(getNextUniqueSymAddressIndex(bitsSizeOf (typeOfLval l)));offsetAddress=(getLvalBits l)}
	
let addLvalToCurrentStackFrame (l:lval) (symLv : symLval) = 
	assert((List.length !symStackFrameItems) > 0);
	let current = getFrameFromStackFrame (List.hd !symStackFrameItems) in
	LvalHashtbl.add current.state l symLv
	
class exprReducerVisitor = object(this)
	inherit nopCilVisitor

	method vexpr (e:exp) = 
		match e with
			| Lval(l) -> 
				(
					match l with
						| Mem e', NoOffset -> 
							(
								match e' with
									| AddrOf l' | StartOf l' -> ChangeTo (Lval(l'))
									| _ -> SkipChildren
							)
						| _ -> SkipChildren
				)
			| _ -> DoChildren
end

let reduceExpr (e:exp) = 
	let vis = new exprReducerVisitor in
	Cil.visitCilExpr vis e
		
class rewriteExpClass = object(this) 
	inherit nopCilVisitor
  
	method private getExprForLval (l:lval) = 
		match (tryFindLvalInCurrentStackFrame l) (*(tryFindLvalInStackFrames l)*) with
			| Some(symLv) -> 
				(
					match symLv.content with
						| SymEx(sex) ->
							(
								match sex with
									| CilExpr(e') -> (true, Some(e'))
									| Undef -> (true, None)
							) 
						| StackAddress(saddr) -> 
							(
								match (tryFindLvalFromStackAddress saddr) with
									| None -> (true, None)
									| Some(l') -> 
										this#getExprForLval l'
							)
				)
			| None -> (false, None)
			 
	method vexpr (e:exp) =
  	match e with
			| AddrOf _ | SizeOfE _ | AlignOfE _ ->
        (* don't rewrite addrof, because this is a constant *)
        SkipChildren
      | StartOf l | Lval l ->
				(
					match (this#getExprForLval l) with
						| (true, None) -> SkipChildren
						| (true, Some(a)) -> 
							ChangeTo a
						| (false, _) -> 
							(
								ChangeDoChildrenPost(e, 
									fun e' -> 
										match (stripCasts e') with
											| StartOf l' | Lval l' -> 
												(
													match (this#getExprForLval l') with
														| (true, Some(a)) -> a
														| _ -> e' 
												)
											| _ -> e'
								)
							)
				)
      | _ -> DoChildren
end

let rewriteExpr (e : exp) =
  let vis = new rewriteExpClass in 
	reduceExpr (constFold true (Cil.visitCilExpr vis e))

let rewriteLval (l:lval)  = 
	let elv = Lval(l) in
	let e = rewriteExpr elv in
	match (stripCasts e) with
		| Lval l' | AddrOf l' | StartOf l' -> l'
		| _ -> l

class containsUndefClass (containsUndef : bool ref) = object(this) 
	inherit nopCilVisitor
  	    
  method vexpr (e : exp) =
		match (stripCasts e) with
			| Lval(l) | AddrOf(l) | StartOf(l) ->
				(
					let symlvO = tryFindLvalInCurrentStackFrame l in
					match symlvO with
						| None -> DoChildren
						| Some(symlv) -> 
							(
								match symlv.content with
									| SymEx(sex) -> 
										(
											match sex with
												| Undef -> containsUndef := true; SkipChildren
												| _ -> DoChildren
										)
									| _ -> DoChildren
							)
				)
			| _ -> DoChildren
end
 
let containsUndefExp (e : exp) =
  let undef = ref false in
  let vis = new containsUndefClass undef
  in (ignore (Cil.visitCilExpr vis e); !undef)

let rec isGlobalVar (l:lval) = 
	match l with
		| Var vi, _ -> vi.vglob
		| Mem e, _ -> isGlobalVarExp e

and isGlobalVarExp (e:exp) = 
	match e with
		| Const _ | SizeOf _ | SizeOfE _ | SizeOfStr _ | AlignOf _ | AlignOfE _ -> false
		| Lval(l) | AddrOf(l) | StartOf(l) -> isGlobalVar l
		| UnOp(_, e',_) -> isGlobalVarExp e'
		| BinOp(_, e1, e2, _) -> 
			let g1 = isGlobalVarExp e1 in
			let g2 = isGlobalVarExp e2 in
			g1 || g2
		| CastE(_, e') -> isGlobalVarExp e'
						
let isLocalVar (l:lval) = 
	match (tryFindLvalInCurrentStackFrame l) with
		| None -> true
		| Some(symlv) -> 
			(
				match symlv.content with
					| SymEx(sex) -> 
						(
							match sex with
								| Undef -> true
								| CilExpr(e) -> not(symlv.isInput)
						)
					| _ -> true
			)
 
let rec containsLocalVars (e:exp) = 
	match e with
		| Const _ | SizeOf _ | SizeOfE _ | SizeOfStr _ | AlignOf _ | AlignOfE _ -> false
		| Lval(l) | AddrOf(l) | StartOf(l) -> lvalContainsLocalVars l
		| UnOp(_, e', _) -> containsLocalVars e'
		| BinOp(_, e1, e2, _) -> 
			let e1local = containsLocalVars e1 in
			let e2local = containsLocalVars e2 in
			e1local || e2local
		| CastE(_, e') -> containsLocalVars e'
		
and lvalContainsLocalVars (l:lval) = 
	match l with
		| Var vi, _ -> isLocalVar l
		| Mem e, _ -> 
			(* if base, i.e. e is a local, then the entire lval is local, otherwise not *)
			containsLocalVars e

let addLvalAsSymbolToFirstStackFrame (l:lval) (f:fundec option) = 
	let len = List.length !symStackFrameItems in
	assert(len > 0);
	let (_,_,first) = List.nth !symStackFrameItems (len - 1) in
	try
		let symlv = LvalHashtbl.find first.state l in
		symlv.content <- (SymEx(CilExpr(Lval(l))));
		symlv.isInput <- true
	with
		| Not_found -> 
			(
				let addr = mkNewSymAddressForLval l in
				let symlv = {symAddr=addr;containingFunc=f;content=(SymEx(CilExpr(Lval(l))));isInput=true} in
				LvalHashtbl.add first.state l symlv
			)
			 			
let updateStateEx (l:lval) (fo:fundec option) (input:bool) (rhs:symContent) = 
	if (List.length !symStackFrameItems) = 0 then (
		Log.log (Printf.sprintf "stack frame empty for %s\n" (Pretty.sprint 255 (Cil.d_lval()l)));
	);
	assert((List.length !symStackFrameItems) > 0);
	let current = getFrameFromStackFrame (List.hd !symStackFrameItems) in
	try
		let symlv = LvalHashtbl.find current.state l in
		symlv.content <- rhs
	with
		| Not_found -> 
			(
				let addr = mkNewSymAddressForLval l in
				let symlv = {symAddr=addr;containingFunc=fo;content=rhs;isInput=input} in
				LvalHashtbl.add current.state l symlv
			)
			
let updateState (lvs : lval list) (fo:fundec option) (rhs : symContent) =
	List.iter(
		fun l -> 
			let isGlob = isGlobalVar l in
			if isGlob then
				updateStateEx l None false rhs
			else
				updateStateEx l fo false rhs
	)lvs
		
let symEnterFunctionSimple (f:fundec) = 
	let newStackFrame = 
		let s' = {state=(LvalHashtbl.create 100)} in
		(Some(f), None, s')
	in
	symStackFrameItems := (newStackFrame::(!symStackFrameItems))

let symExitFunctionSimple () = 
	symStackFrameItems := List.tl (!symStackFrameItems)
			
let symEnterFunction ?(input=false) (f:fundec) (retlo:lval option) (args : exp list) = 
	let currentFunction = 
		if (List.length !symStackFrameItems) = 0 then None
		else (getFunctionFromStackFrame(List.hd !symStackFrameItems))
	in
	let newStackFrame = 
		let s' = {state=(LvalHashtbl.create 100)} in
		List.iter2(
			fun formal arg -> 
				(* for each formal, create a new address. Initialize the contents of the address with the parameters passed *)
				let formalLval = var formal in
				let content = 
					match arg with
						| AddrOf(l) | StartOf(l) ->
							(* find stack address of l *)
							(
								let addrO = tryFindStackAddress l in
								match addrO with
									| None -> 
										(* could not find l in symbolic state, so create a new stack address for l *)
										let symLv = 
											{
												symAddr=(mkNewSymAddressForLval l);
												containingFunc=currentFunction;
												content=(SymEx(Undef));
												isInput=false
											} 
										in
										addLvalToCurrentStackFrame l symLv;
										StackAddress(symLv.symAddr)
									| Some(addr) -> StackAddress(addr)
							)
						| _ -> 
							(* rewrite expr and add *)
							let arg' = rewriteExpr arg in
							SymEx(CilExpr(arg'))
				in
				let fsymLv = 
					{
						symAddr=(mkNewSymAddressForLval formalLval);
						containingFunc=(Some(f));
						content=content;
						isInput=input
					}
				in
				LvalHashtbl.add s'.state formalLval fsymLv
		)f.sformals args;
		(Some(f), retlo, s')
	in
	symStackFrameItems := (newStackFrame::(!symStackFrameItems))

let symExitFunction (eo:exp option) = 
	(*let globalLvals = getCurrentStackFrameGlobals () in*)
	let retlo = getReturnLvalFromStackFrame (List.hd !symStackFrameItems) in
	let contentO = 
		match eo with
			| None -> None
			| Some(e) -> 
				let e' = rewriteExpr e in
				if containsUndefExp e' then (
					Some(SymEx(Undef))
				) else 
					Some(SymEx(CilExpr(e')))
	in
	symStackFrameItems := List.tl (!symStackFrameItems);
	if (List.length (!symStackFrameItems)) > 0 then (
		let (fo, _, current) = (List.hd !symStackFrameItems) in
		match retlo, contentO with
			| (None, _) | (Some _,None) -> ()
			| Some(l), Some(content) -> 
				(* update l with return value *)
				updateState [l] fo content
	)

let printCurrentState () = 
	let printStackAddress (addr:symStackAddress) = 
		Printf.sprintf "base=%d, offset=%d\n" addr.hostAddress addr.offsetAddress
	in
	if (List.length !symStackFrameItems) > 0 then (
		let doc = ref ((++) (text "Symbolic State") line) in
		LvalHashtbl.iter(
			fun lv symlv -> 
				let strStackAddr = printStackAddress symlv.symAddr in
				let strContainingFunc = 
					match symlv.containingFunc with
						| None -> "global variable\n"
						| Some(f) -> Printf.sprintf "local variable in %s\n" f.svar.vname
				in
				let strContent = 
					match symlv.content with
						| StackAddress(addr) -> (printStackAddress addr)
						| SymEx(sex) -> 
							(
								match sex with
									| Undef -> "undefined\n"
									| CilExpr(e) -> Printf.sprintf "%s\n" (Pretty.sprint 255 (Cil.d_exp()e))
							)
				in
				let id = 
					match lv with
						| Var vi, _ -> vi.vid
						| _ -> 0
				in
				let str = 
					Printf.sprintf "%s%sisInput=%s\n%d:%s = %s\n"
						strStackAddr
						strContainingFunc
						(string_of_bool symlv.isInput)
						id
						(Pretty.sprint 255 (Cil.d_lval () lv))
						strContent
				in
				doc := (++) (!doc) (text str)
		)(getFrameFromStackFrame(List.hd !symStackFrameItems)).state;
		!doc
	) else
		nil
						
let isValueExp (e : exp) =
  match isInteger e with | None -> isConstant e | _ -> false

let updatePathCondition (e:exp) (sid:int) (index:int) = 
	if not(isConstant e) then (
		pc.conjuncts <- (pc.conjuncts @ [(sid,index,e)]);
		if pc.pathExpression = one then
			pc.pathExpression <- e
		else
			pc.pathExpression <- BinOp(LAnd, pc.pathExpression, e, (typeOf e))
	)	

let getCurrentFunction () = 
	if (List.length !symStackFrameItems) = 0 then None
	else (
		getFunctionFromStackFrame(List.hd !symStackFrameItems)
	)
		
let makeLvalUndef (lvs:lval list) (f:fundec) =
	List.iter(
		fun l -> 
			match (tryFindLvalInCurrentStackFrame l) with
				| None -> ()
				| Some(symlv) -> 
					symlv.content <- SymEx(Undef)
	)lvs
	
let makeExpUndef (exs:exp list) (f:fundec) = 
	List.iter(
		fun e -> 
			let e' = rewriteExpr e in
			match (stripCasts e') with
				| AddrOf(l) | StartOf(l) | Lval(l) -> makeLvalUndef [l] f
				| _ -> ()
	)exs
	
let isComparisonOp (b : binop) =
  match b with | Lt | Gt | Le | Ge | Eq | Ne -> true | _ -> false
  
let isInfeasibleBinOp (e1 : exp) (e2 : exp) =
  match (e1, e2) with
  | (BinOp (b1, e1', e1'', _), BinOp (b2, e2', e2'', _)) ->
      if (not (isComparisonOp b1)) || (not (isComparisonOp b2))
      then false
      else
        if b1 = b2
        then
          if (b1 = Eq) || (b1 = Ne)
          then false
          else (compareExp e1' e2'') && (compareExp e1'' e2')
        else
          if (compareExp e1' e2') && (compareExp e1'' e2'')
          then
            (match (b1, b2) with
             | (Lt, Ge) | (Le, Gt) | (Gt, Le) | (Ge, Lt) -> true
             | (_, _) -> false)
          else
            if (compareExp e1' e2'') && (compareExp e1'' e2')
            then
              (match (b1, b2) with
               | (Gt, Ge) | (Ge, Gt) | (Lt, Le) | (Le, Lt) -> true
               | (_, _) -> false)
            else false
  | (_, _) -> false
  
let isInfeasibleUnOp (e1 : exp) (e2 : exp) =
  match (e1, e2) with
  | (UnOp _, UnOp _) | (UnOp _, BinOp _) | (BinOp _, UnOp _) -> false
  | (UnOp (u1, e1', _), _) -> if u1 = LNot then (compareExp e1' e2) else false
  | (_, UnOp (u2, e2', _)) -> if u2 = LNot then (compareExp e1 e2') else false
  | _ -> false

let rec tryInvertOp (e : exp) =
  match e with
  | BinOp (b, e1, e2, t) ->
      let b' = invertRelBinaryOp b in
			BinOp (b', e1, e2, t)
  | UnOp (u, e', t) ->
      (match u with | LNot -> e' | _ -> BinOp (Eq, e, zero, t))
	| CastE(t, e') -> mkCast (tryInvertOp e') t
	| Lval _ | StartOf _  -> BinOp (Eq, e, zero, typeOf e)
	| _ -> e
  
let getIfExp (s : stmt) (edge : int) =
  match s.skind with
  | If (e, th, el, loc) -> if edge = 1 then e else tryInvertOp e
  | _ -> 
		Log.error (sprintf "Statement %d (edge %d) is not an If statement\n" s.sid edge)

let isInfeasiblePath (path : exp list) =
  let hasSyntacticNegation (e : exp) =
    List.exists
      (fun e' ->
         if not(compareExp e e')
         then (isInfeasibleBinOp e e') || (isInfeasibleUnOp e e')
         else false)
      path
  in List.exists hasSyntacticNegation path
		 		
let printPathCondition () = 
	text (Printf.sprintf "Path Condition: %s" (Pretty.sprint 255 (Cil.d_exp () pc.pathExpression)))

let finalCleanup () = 
	symStackFrameItems := [];
	pc.conjuncts <- []
;;	
at_exit finalCleanup;;