(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open Printf
open Utils

open TraceManager

module Log = LogManager

let ulonglongType = TInt(IULongLong, [])
let longlongType = TInt(ILongLong, [])
let longdblType = TFloat(FLongDouble, [])
let constCharPtrTypeSig = (typeSig charConstPtrType)
(* const char* s *)
let constCharPtrType = TPtr(TInt(IChar, []),[Attr("const",[])])

let prototypeFundecs = ref []

let reset() = 
	prototypeFundecs := []
	
let addPrototype (f:fundec) = 
	let namesMatch (f':fundec) = (compare f'.svar.vname f.svar.vname) = 0 in
	if not(List.exists namesMatch (!prototypeFundecs)) then
		prototypeFundecs := (f::(!prototypeFundecs));
;;
		
let mkAddrCast (e:exp) = mkCast e voidPtrType
let mkOffsetCast (e:exp) = mkCast e uintType
let mkFloatValueCast (e:exp) = mkCast e longdblType
let mkIntValueCast (e:exp) = mkCast e longlongType
let mkPointerValueCast (e:exp) = mkCast e voidPtrType

let mkAustinVarArgCall (name:string) = 
	let f = emptyFunction name in
	f.svar.vtype <- TFun(voidType, Some[
		("sid", uintType, []);
		("len", uintType, []);
	], true, []);
	addPrototype f;
	f
	
let mkAustinLogBranch (name:string) = 
	let f = emptyFunction name in
	f.svar.vtype <- TFun(voidType, Some[
		("sid", uintType, []);
		("index", uintType, []);
		("len", uintType, []);
	], true, []);
	addPrototype f;
	f
	
let rec tryFindLvalFromExp (e:exp) = 
	match (stripCasts e) with
		| Lval(l) | AddrOf(l) | StartOf(l) -> Some(l)
		| CastE(_,e') -> tryFindLvalFromExp e'
		| _ -> None

let rec mkAddrOfExpr (e:exp) = 
	if isConstant e then
		Cil.zero
	else (
		match (tryFindLvalFromExp e) with
			| None -> 
				(
					match e with
						| UnOp(_, _, t) -> 
							if (isPointerType t) then e else Cil.zero 
						| BinOp(_, _, _, t) -> if (isPointerType t) then e else Cil.zero
						| _ -> Cil.zero
				)
			| Some(lh,lo) -> 
				if not(isBitfield lo) then (
					mkAddrOrStartOf (lh,lo)
				) else (
					(* get base and use base address *)
					match (lh,lo) with
						| Var v, Field _ -> mkAddrOrStartOf (var v)
						| Mem be, Field _ -> mkAddrOfExpr be
						| _ -> Log.error (Printf.sprintf "Encountered bitfield, but offset does not match Field:%s\n" (Pretty.sprint 255 (Cil.d_exp()e)))  
				)
	)
	
let mkOffsetOfExpr (e:exp) =  	
	match (tryFindLvalFromExp e) with
		| None -> integer 0
		| Some(l) -> 
			(
				let _,offset,_ = Utils.addrAndBitOffset l in
				offset
				(*match (lh,lo) with
					| Var vi, Field _ -> integer (fst(bitsOffset vi.vtype lo))
					| Mem e', Field _ -> integer (fst(bitsOffset (typeOf e') lo))
					| _,_ -> Cil.zero*)
				(*match (lh,lo) with
					| Var vi, _ -> integer (fst(bitsOffset vi.vtype lo))
					| Mem e', _ -> 
						integer (fst(bitsOffset (typeOf e') lo))*)
			)

let rec mkValueExpr (t:typ) (e:exp) = 
	match t with
		| TVoid _-> Const(CStr("d")), (mkIntValueCast Cil.zero)
		| TInt _ -> Const(CStr("d")), (mkIntValueCast e)
		| TFloat _ -> Const(CStr("f")), (mkFloatValueCast e)
		| TPtr(t', _) -> 
			(*
			if not(isPointerType (unrollType t')) &&
				 isPointerDerefEx e then (
				mkValueExpr t' e
			) else *)
				Const(CStr("p")), (mkPointerValueCast e)
		| TArray _ -> Const(CStr("d")), (mkIntValueCast Cil.zero)
		| TFun _ -> Const(CStr("d")), (mkIntValueCast Cil.zero)
		| TNamed(ti, _) -> mkValueExpr ti.ttype e
		| TComp(_, _) -> Const(CStr("d")), (mkIntValueCast Cil.zero)
		| TEnum _ -> Const(CStr("d")), (mkIntValueCast e)
		| TBuiltin_va_list _ -> Const(CStr("d")), (mkIntValueCast Cil.zero)		
	
let rec mkFormatStringAndValuesFromExp (e:exp) = 
	let address = mkAddrCast (mkAddrOfExpr e) in
	let offset = 	mkOffsetCast (mkOffsetOfExpr e) in
	let t = typeOf e in
	let targetAddr = 
		if not(isPointerType t) || (isConstant e) then 
			mkAddrCast Cil.zero
		else (
			match (tryFindLvalFromExp e) with
				| None -> mkAddrCast e
				| Some(lh,lo) -> 
					(
						match (lh,lo) with
							| Mem e', NoOffset -> mkAddrCast e' (* e.g. *p -> p *)
							| Mem e', Field(fi, _) -> 
								(* either p->next in which case p->next or p->v in which case 0 *)
								if (isPointerType (unrollType fi.ftype)) then mkAddrCast e else mkAddrCast Cil.zero
							| Mem e', Index _ -> mkAddrCast e
							| Var vi, _ -> mkAddrCast e
					)
		)
	in
	let fmt, value = mkValueExpr t e in
	[address;offset;targetAddr;fmt;value]
			 
class symInstrVisitor (ignoreList:string list) (source:file) = object(this)
	inherit nopCilVisitor
	
	val austinLogStmtFundec = mkAustinVarArgCall "Austin__SymLogStmt"
	val austinLogCallFundec = mkAustinVarArgCall "Austin__SymLogCall"
	val austinLogReturn = mkAustinVarArgCall "Austin__SymLogReturn"
	val austinLogReturnValue = mkAustinVarArgCall "Austin__SymUpdateReturn"
	val austinLogBranch = mkAustinLogBranch "Austin__SymLogBranch"
		 	
	method private mkAustLogStmtCall (sid:int) (len:int) (args:exp list) =
		Call(None, Lval((var austinLogStmtFundec.svar)), 
			((integer sid)::(integer len)::args), locUnknown)
	
	method private mkAustLogCallCall (sid:int) (len:int) (paralist:exp list) = 
		Call(None, Lval((var austinLogCallFundec.svar)), 
			((integer sid)::(integer len)::paralist), locUnknown)
	
	method private mkAustLogReturn (sid:int) (len:int) (args:exp list) = 
		Call(None, Lval((var austinLogReturn.svar)), 
			((integer sid)::(integer len)::args), locUnknown)
			
	method private mkAustLogReturnUpdate (sid:int) (len:int) (args:exp list) = 
		Call(None, Lval((var austinLogReturnValue.svar)), 
			((integer sid)::(integer len)::args), locUnknown)
	
	method private getArgsForBranchingNode (e:exp) = 
		match (stripCasts e) with
			| UnOp(u,e',t) -> 
				(
					(1, (mkFormatStringAndValuesFromExp e))
				)
			| BinOp(b,e1,e2,t) -> 
				(
					match b with
						| Lt | Gt | Le | Ge | Eq | Ne -> 
							(
								let lhs = mkFormatStringAndValuesFromExp e1 in
								let rhs = mkFormatStringAndValuesFromExp e2 in
								(2, (lhs@rhs))
							)
						| _ -> (1, (mkFormatStringAndValuesFromExp e))
				)
			| Lval(l) | StartOf(l) | AddrOf(l) -> 
				(
					(1, (mkFormatStringAndValuesFromExp e))
				)
			| CastE(t,e') -> this#getArgsForBranchingNode e'
			| _ -> (* ignore *) (0,[])
			 
	method private mkAustinLogBranch (sid:int) (index:int) (len:int) (args:exp list) = 
		  Call(None, Lval((var austinLogBranch.svar)), 
			((integer sid)::(integer index)::(integer len)::args), locUnknown)
	
	method vstmt (s:stmt) = 
		match s.skind with
			| Instr(ilist) -> 
				assert((List.length ilist) < 2);
				if ((List.length ilist) > 0) then (
					let i = List.hd ilist in
					match i with
						| Set(l,e, _) -> 
							let lhs = mkFormatStringAndValuesFromExp (Lval(l)) in
							let rhs = mkFormatStringAndValuesFromExp e in
							let i' = this#mkAustLogStmtCall s.sid 2 (lhs@rhs) in
							pushInstrBeforeStmt s [i']
						| Call(lo, f, args, _) -> 
							(
								let fname = Pretty.sprint 255 (Cil.d_exp()f) in
								if not(startsWith "Austin__" fname) &&
									 not(endsWith "__mock" fname) then ( 
									let len = List.length args in
									let paras = List.fold_left(
										fun res arg -> 
											let _a = mkFormatStringAndValuesFromExp arg in
											(res@(_a))	
										)[] args
									in
									match lo with
										| None -> (* just log call, i.e. queueInstr *)
											let i' = this#mkAustLogCallCall s.sid len paras in
											pushInstrBeforeStmt s [i']
										| Some(l) -> 
											let lhs = mkFormatStringAndValuesFromExp (Lval(l)) in
											let preI = this#mkAustLogCallCall s.sid len paras in
											let postI = this#mkAustLogReturnUpdate s.sid 1 lhs in
											pushInstrBeforeStmt s [preI];
											appendInstr s [postI]
											(*s.skind <- Instr([preI;i;postI])*)
								)
							)
						| _ -> ()
				);
				SkipChildren
			| If(e, tb, fb, l) -> 
				(* call Austin__SymLogBranch(int sid, unsigned int index, const char* format, ...) *)
				let len, args = this#getArgsForBranchingNode e in
				let trueI = this#mkAustinLogBranch s.sid 0 len args in
				let falseI = this#mkAustinLogBranch s.sid 1 len args in
				ChangeDoChildrenPost(s, fun s' -> 
					addInstrsToBlock tb [trueI];
					addInstrsToBlock fb [falseI];
					s')
			| Switch(e, _, cases, _) -> 
				let insertCaseLoggingFunctions () = 
					let index = ref 0 in
					let caseswodef = removeDefaultCase cases in
					let len, args = this#getArgsForBranchingNode (BinOp(Eq, e, e, (typeOf e))) in
					List.iter(
						fun caseStmt ->
							(* I am not interested in case labels, because at runtime I just want to know the value of e *)
							let i' = this#mkAustinLogBranch s.sid (!index) len args in
							pushInstrBeforeStmt caseStmt [i'];(*
							let vis = new insertInstrVisitor i' in
							ignore(visitCilStmt vis caseStmt);*)
							incr index
					) caseswodef;
					(
						match (tryGetDefaultCase cases) with
							| None -> ()
							| Some(s') -> 
								let i' = this#mkAustinLogBranch s.sid (!index) len args in
								pushInstrBeforeStmt s' [i']
								(*let vis = new insertInstrVisitor i' in
								ignore(visitCilStmt vis s');*)
					)
				in
				ChangeDoChildrenPost(s, fun s' -> insertCaseLoggingFunctions();s')
			| Return(eo, _) -> 
				(
					match eo with
						| None -> ()
						| Some(e) -> 
							let expr = mkFormatStringAndValuesFromExp e in
							let i' = this#mkAustLogReturn s.sid 1 expr in
							pushInstrBeforeStmt s [i']
				); SkipChildren
			| _  -> DoChildren

	method vfunc (f:fundec) = 
		if (List.mem f.svar.vname ignoreList) || (startsWith "Austin__" f.svar.vname) ||
			 (endsWith "__mock" f.svar.vname)then
			SkipChildren
		else (
			DoChildren
		)
end
let mkSymexTraceCallFunction () = 
	let f = emptyFunction "Austin__SymexTrace" in
	f.svar.vtype <- TFun(voidType, None, false, []);
	Call(None, Lval((var f.svar)), [], locUnknown)
	
let main (source:file) (ignoreList:string list) = 
	let vis = new symInstrVisitor ignoreList source in
	visitCilFileSameGlobals vis source;
	(!prototypeFundecs, [mkSymexTraceCallFunction()])
	