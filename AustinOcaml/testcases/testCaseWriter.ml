(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open Solution

let flags = [Open_creat;Open_append;Open_text]
let perm = 0o755 
	
let mallocExpr = 
	let v = makeVarinfo false "malloc" (TFun(voidPtrType, Some["size", uintType, []], false, [])) in
	Lval(var v)
	
let freeExpr = 
	let v = makeVarinfo false "free" (TFun(voidType, Some["size", voidPtrType, []], false, [])) in
	Lval(var v)
		
let saveCandidateSolution (id:int) (sol : candidateSolution) (comment:string) (testdrv:fundec) (fut:fundec) = 
	let oc = open_out_gen flags perm (ConfigFile.find Options.keyTestCaseFile) in
	let testcaseFunc = emptyFunction (Printf.sprintf "%s_testcase_%d" fut.svar.vname id) in
	testcaseFunc.svar.vtype <- TFun(voidType, Some[], false, []);
	
	let mallocList = ref [] in
	let freelist = ref [] in
	
	testcaseFunc.slocals <- List.map(fun v -> v)testdrv.slocals;

  let mkFreeStmt (l:lval) = 
		let thn = 
			mkBlock [mkStmtOneInstr (Call(None, freeExpr, [Lval(l)], locUnknown))]
		in
		let els = mkBlock [] in
		let kind = If(Lval(l),thn,els,locUnknown) in
		mkStmt kind
	in
	let assignValue (l:lval) (in_node:inputNode) = 
		let getMallocType () = 
			match unrollType (typeOfLval l) with
				| TPtr(pt, _) -> pt
				| _ -> typeOfLval l
		in
		match in_node with
			| IntNode(_in) -> 
				(
					let ikind = intKindForValue _in.ival (Utils.isUnsignedType (typeOfLval l)) in
					[Set(l, (Const(CInt64(_in.ival,ikind,None))), locUnknown)]
				)
			| FloatNode(_fn) -> 
				(
					let fkind = 
						match unrollType (typeOfLval l) with
							| TFloat(fk,_) -> fk
							| _ -> Log.error "Wrong float type for FloatNode\n"
					in
					[Set(l, (Const(CReal(_fn.fval,fkind,None))), locUnknown)]
				)
			| PointerNode(_pn) -> 
				if _pn.pointToNull then 
					[Set(l, (CastE(voidPtrType, Cil.zero)), locUnknown)]
				else if _pn.targetNodeId = (-1) then (
					let e = SizeOf(getMallocType ()) in
					freelist := ((mkFreeStmt l)::!freelist);
					mallocList := (!mallocList @ [Call(Some(l), mallocExpr, [e], locUnknown)]);
					[]
				) else (
					if _pn.isPointerToArray then (
						let e = BinOp(Mult, (integer _pn.firstArrayDim), SizeOf(getMallocType ()), uintType) in
						
						freelist := ((mkFreeStmt l)::!freelist);
						
						mallocList := (!mallocList @ [Call(Some(l), mallocExpr, [e], locUnknown)]);
						[]
					) else (
						match (sol#tryFindNodeFromNodeId _pn.targetNodeId) with
							| None -> Log.error (Printf.sprintf "Failed to find lval from %d\n" _pn.targetNodeId)
							| Some(target) -> 
								if _pn.takesAddrOf then
									[Set(l, (mkAddrOrStartOf target.cilLval), locUnknown)]
								else
									[Set(l, Lval(target.cilLval), locUnknown)]
					)
				)
	in
	
	let assignments = List.fold_left(
		fun res node -> 
			(*addLvalLocalVars node.cilLval fut;*)
			(res @ (assignValue node.cilLval node.node))
	)[] (sol#getInputList())
	in
	let futArgs = List.map(fun v -> Lval(var v))fut.sformals in
	let hasReturn = ref false in
	let eRetVal, callToFut = 
		match unrollType fut.svar.vtype with
			| TFun(rt, _, _, _) -> 
				(
					testcaseFunc.svar.vtype <- TFun(rt, Some[], false, []);
					match (unrollTypeDeep rt) with
						| TVoid _ -> 
							(Cil.zero, [Call(None, (Lval(var fut.svar)), futArgs, locUnknown)])
						| _ ->
							hasReturn := true;
							let tmp = makeTempVar testcaseFunc rt in
							(Lval(var tmp), [Call(Some((var tmp)), (Lval(var fut.svar)), futArgs, locUnknown)])  
				)
			| _ -> 
				(Cil.zero, [Call(None, (Lval(var fut.svar)), futArgs, locUnknown)])
	in
	let body = 
		let p1 = (mkStmt (Instr((!mallocList @ assignments @ callToFut))))::(!freelist) in
		if !hasReturn then
			(p1 @ [(mkStmt (Return(Some(eRetVal), locUnknown)))])
		else
			p1
	in
	testcaseFunc.sbody <- (mkBlock body);
	let glob = GFun(testcaseFunc, locUnknown) in
	output_string oc ("\r\n/* "^comment^" */\r\n");
	output_string oc (Printf.sprintf "%s\r\n" (Pretty.sprint 255 (Cil.d_global () glob)));
	close_out oc;
	id