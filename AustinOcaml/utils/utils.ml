(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil

module Log = LogManager

let convertDotToPng (fileName : string) = 
	let cmd = "dot -Tpng "^fileName^".dot > "^fileName^".png" in
	Sys.command cmd
	
let printCFG (source : file) = 
		
	List.iter(
		fun global -> 
			match global with
				| GFun(func, loc) ->
					let fileName = func.svar.vname(* the name of the function *)^"_cfg" in
					let oc = open_out (fileName^".dot") in 
					Cfg.printCfgChannel oc func;
					close_out oc;
					ignore(convertDotToPng fileName);
				| _ -> ()
	)source.globals

let marshalSource (source:file) (filename:string) =
	let outchan = open_out_bin filename in
  Marshal.to_channel outchan source [];
  close_out outchan
	
let unmarshalSource (filename:string) = 
	let inchan = open_in_bin filename in
  let loaded : file = (Marshal.from_channel inchan : file) in
  close_in inchan ;
  loaded

let loadFundecFromFile (filename : string) =
	let inchan = open_in_bin filename in
  let f = (Marshal.from_channel inchan : fundec) in
  close_in inchan;
	f
		
let tryGetAttribute (name : string) (attr : attributes) = 
	try
		let a = 
			List.find(
				fun a' -> 
					match a' with
						| Attr(n, paras) -> n = name 
			) attr 
		in
		Some(a)
	with
		| Not_found -> None

let tryFindFundec (e : exp) (source : file) =
	let targetName = 
		match e with
			| Lval(lh,lo) -> 
				(
					match lh with
						| Var(vi) -> vi.vname
						| _ -> "" 
				)
			| _ -> ""
	in
	if targetName = "" then None
	else (
		try
			let glbl = 
				List.find(
					fun g -> 
						match g with
							| GFun(fdec, _) -> (compare fdec.svar.vname targetName) = 0
							| _ -> false
				) source.globals
			in
			match glbl with
				| GFun(f,_) -> Some(f)
				| _ -> None
		with
			| Not_found -> None
	)
	
let rec tryFindFundecFromName (source : file) (name : string) = 
	let rec walkGlobals (globs:global list) = 
		match globs with
			| [] -> None
			| g::rem -> begin
					match g with 
						| GFun(fdec,_) when fdec.svar.vname = name -> Some(fdec)
						| _ -> walkGlobals rem
				end
	in
	walkGlobals source.globals

class lvalExpVisitor (todo) = object
	inherit nopCilVisitor 
	method vlval(l:lval) = 
		ChangeTo (todo l) (*(normalizeArrayAccess l)*)
end

let makeArrayAccess (l:lval) (index:exp) = 
	let start = 
		if (isPointerType (typeOfLval l)) then 
			Lval(l)
		else
			mkAddrOrStartOf l 
	in
	let addition = BinOp(IndexPI, start, index, (typeOf start)) in
	mkMem addition NoOffset
	
let rec normalizeArrayAccessEx (e:exp) = 
	let vis = new lvalExpVisitor normalizeArrayAccess in
	visitCilExpr vis e
and normalizeArrayAccess ((lh,off):lval) =
	match off with
		| Index(e,off') ->
			(
				let l', _ = removeOffsetLval (lh,off) in
				makeArrayAccess l' e
			) 
		| _ -> (lh,off)
				
let rec compareExp (e1: exp) (e2: exp) : bool =
  (*log "CompareExp %a and %a.\n" d_plainexp e1 d_plainexp e2; *)
  e1 == e2 ||
  match e1, e2 with
		| Lval lv1, StartOf lv2
		| StartOf lv1, Lval lv2 -> 
			compareLval lv1 lv2 
	  | Lval lv1, Lval lv2
	  | StartOf lv1, StartOf lv2
	  | AddrOf lv1, AddrOf lv2 -> compareLval lv1 lv2
	  | BinOp(bop1, l1, r1, _), BinOp(bop2, l2, r2, _) ->
	      bop1 = bop2 && compareExp l1 l2 && compareExp r1 r2
	  | CastE(t1, e1), CastE(t2, e2) ->
	    	compareType t1 t2 && compareExp e1 e2
	  | _ -> begin
	      match isInteger (constFold true e1), isInteger (constFold true e2) with
	        Some i1, Some i2 -> i1 = i2
	      | _ -> false
	    end
and compareType (t1:typ) (t2:typ) : bool = 
	t1 == t2 ||
	match t1,t2 with
		| TVoid _,TVoid _ -> true
		| TInt(ikind1,_),TInt(ikind2,_) -> ikind1 = ikind2
		| TFloat(fkind1,_),TFloat(fkind2,_) -> fkind1 = fkind2
		| TPtr(pt1,_),TPtr(pt2,_) -> compareType pt1 pt2
		| TArray(at1,eo1,_),TArray(at2,eo2,_) -> 
			let eomatch = 
				match eo1,eo2 with
					| Some(e1),Some(e2) -> compareExp e1 e2
					| None,None -> true
					| _,_ -> false
			in
			eomatch && compareType at1 at2 
		| TNamed(ti1,_),TNamed(ti2,_) -> 
			ti1.tname = ti2.tname && 
			compareType ti1.ttype ti2.ttype && 
			ti1.treferenced == ti2.treferenced
		| TComp(ci1,_),TComp(ci2,_) -> compareCompInfo ci1 ci2
		| TEnum(ei1,_),TEnum(ei2,_) -> compareEnumInfo ei1 ei2
		| _,_ -> false
and compareCompInfo (ci1:compinfo) (ci2:compinfo) = 
	ci1 == ci2 || (
		ci1.cstruct == ci2.cstruct && 
		ci1.cname   =  ci2.cname   && 
		ci1.ckey    == ci2.ckey    &&
		(List.length ci1.cfields) == (List.length ci2.cfields) && 
		not(List.exists2(fun f1 f2 -> 
			f1.fname <> f2.fname)ci1.cfields ci2.cfields)  &&
		ci1.cdefined == ci2.cdefined &&
		ci1.creferenced == ci2.creferenced 
	) 
and compareFieldInfo (fi1:fieldinfo) (fi2:fieldinfo) = 
	fi1 == fi2 || (
		fi1.fcomp.cname = fi2.fcomp.cname &&
		fi1.fname       = fi2.fname       &&
		compareType fi1.ftype fi2.ftype   &&
		fi1.fbitfield   = fi2.fbitfield   &&
		fi1.floc        = fi2.floc		
	)
and compareEnumInfo (ei1:enuminfo) (ei2:enuminfo) = 
	ei1 == ei2 || (
		ei1.ename = ei2.ename &&
		(List.length ei1.eitems) == (List.length ei2.eitems) && 
		not(List.exists2(fun (n1,v1,_) (n2,v2,_) -> n1 <> n2 || not(compareExp v1 v2))ei1.eitems ei2.eitems) &&
		ei1.ereferenced == ei2.ereferenced && 
		ei1.ekind = ei2.ekind
	)
and compareVarinfo (vi1:varinfo) (vi2:varinfo) = 
	vi1 == vi2 || (
		vi1.vname = vi2.vname &&
		compareType vi1.vtype vi2.vtype &&
		vi1.vstorage = vi2.vstorage &&
		vi1.vglob   == vi2.vglob &&
		vi1.vinline == vi2.vinline &&
		vi1.vdecl = vi2.vdecl &&
		vi1.vid == vi2.vid &&
		vi1.vaddrof == vi2.vaddrof &&
		vi1.vreferenced == vi2.vreferenced
	)
and compareLval (lv1: lval) (lv2: lval) : bool =
  let rec compareOffset (off1: offset) (off2: offset) : bool =
    match off1, off2 with
    | Field (fld1, off1'), Field (fld2, off2') -> 
        compareFieldInfo fld1 fld2 && compareOffset off1' off2'
    | Index (e1, off1'), Index (e2, off2') ->
        compareExp e1 e2 && compareOffset off1' off2'
    | NoOffset, NoOffset -> true
    | _ -> false
  in
  lv1 == lv2 ||
  match lv1, lv2 with
  | (Var vi1, off1), (Var vi2, off2) ->
      compareVarinfo vi1 vi2 && compareOffset off1 off2
  | (Mem e1, off1), (Mem e2, off2) ->
      compareExp e1 e2 && compareOffset off1 off2
  | _ -> false
		
let compareExpStripCasts (e1: exp) (e2: exp) : int =
	if (compareExp (Expcompare.stripNopCasts e1) (Expcompare.stripNopCasts e2)) then 0
	else compare e1 e2
	 
let isVarargFunc (f:fundec) = 
	match f.svar.vtype with
		| TFun(_, _, vararg, _) -> vararg
		| _ -> false

let isComparisonOp (b : binop) =
  match b with | Lt | Gt | Le | Ge | Eq | Ne -> true | _ -> false
	
class findArrayLengthLvalVis (vref:varinfo ref) (target : string) = object(this)
	inherit nopCilVisitor
	
	method vvrbl (v:varinfo) = 
		if v.vname = target then (
			vref := v;
			SkipChildren
		) else
			DoChildren
end

let tryGetArrayLengthFromParas (p:attrparam list) (source:file) = 
	let rec searchParas (aparas : attrparam list) =
		 match aparas with
			| [] -> (false, zero)
			| para::rem -> 
				(
					match para with 
						| AInt(i) -> (true, (integer i))
						| AStr(s) -> 
							(
								let vdummy = ref (makeVarinfo false "@dummy" intType) in
								let vis = new findArrayLengthLvalVis vdummy s in
								visitCilFileSameGlobals vis source;
								assert(!vdummy.vname <> "@dummy");
								(true, (Lval((var (!vdummy)))))
							)
						| _ -> searchParas rem
				)
	in
	searchParas p
	
let rec isPointerDerefEx (e:exp) = 
	match (stripCasts e) with
		| Lval(l) -> isPointerDeref l
		| _ -> false
and isPointerDeref (l:lval) = 
	match l with
		| Mem e, Field(fi,fo) -> 
			if isPointerType(unrollType fi.ftype) then false
			else true
		| Mem e, NoOffset -> true
		| _ -> false
						
let rec getBits lo = match lo with
	| NoOffset -> None
  | Field(fi,NoOffset) -> fi.fbitfield
  | Field(_,lo) -> getBits lo
  | Index(_,lo) -> getBits lo

let rec adjustTypeLimit (t:typ) (bits:int) = 
	let ikindLimit (kind:ikind) = 
		match kind with
			| ILong | IULong | ILongLong | IULongLong -> 
				if bits >= 64 then 63 else bits
			| _ -> if bits >= 32 then 31 else bits
	in
	match (unrollType t) with
		| TInt(kind, _) -> ikindLimit kind
		| TFloat _ -> if bits >= 64 then 64 else bits
		| TNamed(ti,_) -> adjustTypeLimit ti.ttype bits
		| TEnum(ei, _) -> ikindLimit ei.ekind
		| _ -> bits
	
let getLvalBits (l:lval) = 
	match l with
		| _, o -> 
			let lt = typeOfLval l in
			let bits = 
				match (getBits o) with
					| None -> bitsSizeOf lt
					| Some(b) -> b
			in
			adjustTypeLimit lt bits
			
let rec isBitfield lo = 
	not((getBits lo) = None) 

let rec isCompInfo (t:typ) = 
	let t' = unrollType t in
	match t' with
		| TComp _ -> true
		| TPtr(t'', _) -> isCompInfo t''
		| _ -> false

let rec isUnsignedType (t:typ) = 
	match t with
		| TInt(ikind, _) -> 
			(
				match ikind with
					| IUChar | IUInt | IUShort | IULong | IULongLong -> true
					| _ -> false
			)
		| TPtr(pt, _) -> isUnsignedType pt
		| TArray(at, _, _) -> isUnsignedType at
		| _ -> false
	
let rec isCompleteType_Austin t =
  match unrollType t with
  | TArray(t, None, _) -> false
  | TArray(t, Some z, _) when isZero z -> false
  | TComp (comp, _) -> (* Struct or union *)
	  comp.cdefined && List.for_all (fun fi -> isCompleteType fi.ftype) comp.cfields
  | _ -> true
	 	
let ikindToString (kind : ikind) = 
	match kind with
		| IChar -> "Char"
		| ISChar -> "SChar"
		| IUChar -> "UChar"
		| IBool -> "Bool"
		| IInt -> "Int"
		| IUInt -> "UInt"
		| IShort -> "Short"
		| IUShort -> "UShort"
		| ILong -> "Long"
		| IULong -> "ULong"
		| ILongLong -> "LongLong"
		| IULongLong -> "ULongLong"

let fkindToString (kind : fkind) = 
	match kind with
		| FFloat -> "Float"
		| FDouble -> "Double"
		| FLongDouble -> "LongDouble"	

let invertRelBinaryOp (b:binop) = 
	match b with
		| Lt -> Ge
		| Gt -> Le
		| Le -> Gt
		| Ge -> Lt
		| Eq -> Ne
		| Ne -> Eq
		| _ -> b
	 				
class propagateNegationVisitor = object(this)
	inherit nopCilVisitor 
	
	method private invert (e:exp) = 
		match e with
			| BinOp(b,l,r,t) -> 
				(
					match b with
						| Lt -> BinOp(Ge, l, r, t)
						| Gt -> BinOp(Le, l, r, t)
						| Le -> BinOp(Gt, l, r, t)
						| Ge -> BinOp(Lt, l, r, t)
						| Eq -> BinOp(Ne, l, r, t)
						| Ne -> BinOp(Eq, l, r, t)
						| _ -> BinOp(Ne, e, zero, intType)
				)
			| UnOp(u,e',t) -> 
				(
					match u with
						| LNot -> BinOp(Ne, e', zero, intType)
						| _ -> BinOp(Eq, e, zero, intType)
				)
			| CastE(t,e') -> 
				CastE(t,(this#invert e'))
			| _ -> (* becomes !e -> e == 0*) BinOp(Eq, e, zero, intType)
			 
	method vexpr (e:exp) = 
		match e with
			| UnOp(u,e',t) -> 
				ChangeDoChildrenPost(e',(fun e'' -> this#invert e''))
			| _ -> DoChildren
end

let propagateNegation (e:exp) = 
	let vis = new propagateNegationVisitor in
	visitCilExpr vis e
	
let compareConstants (c1:constant) (c2:constant) = 
	match c1,c2 with
		| CInt64(v1, _, _), CInt64(v2, _, _) -> compare v1 v2
		| CStr(s1), CStr(s2) -> compare s1 s2
		| CWStr(i1l), CWStr(i2l) -> 
			if (List.length i1l) <> (List.length i2l) then compare (List.length i1l) (List.length i2l)
			else if (List.length i1l) = 0 && (List.length i2l) = 0 then
				0
			else (
				if not(List.exists2 (fun i1 i2 -> i1 <> i2) i1l i2l) then 0
				else -1  
			)
		| CChr(c1), CChr(c2) -> compare c1 c2
		| CReal(f1, _, _), CReal(f2, _, _) -> compare f1 f2
		| CEnum(e1,_,_),CEnum(e2,_,_) -> 
			if (compareExp e1 e2) then 0 else compare e1 e2
		| _ -> compare c1 c2

let rec stripCastsEx (e: exp) (casts : typ list) = 
	match e with 
		| CastE(t, e') -> stripCastsEx e' (t::casts) 
		| _ -> (e, casts)

let reapplyCasts (e:exp) (revCasts:typ list) = 
	List.fold_left (fun e' castT -> CastE(castT, e')) e (List.rev revCasts)
	
let addrAndBitOffset ((lh,lo) : lhost * offset) = 
  
	if isBitfield lo then (
    let baseLval, trimmedOffset = removeOffsetLval (lh, lo) in
		let addrOf = mkAddrOrStartOf baseLval in
		let offset,width = 
			match trimmedOffset with
				| NoOffset -> zero,(integer (bitsSizeOf (typeOfLval (lh,lo))))
				| _ -> 
					let enclosingType = typeOfLval baseLval in
					let o, w = bitsOffset enclosingType trimmedOffset in
					(integer o), (integer w) 
		in
		(addrOf, offset, width)
  ) else (
		(mkAddrOrStartOf (lh,lo)), zero, (integer (bitsSizeOf (typeOfLval (lh,lo))))
	)

let removeDefaultCase (cases : stmt list) = 
	let rec hasCaseLabel (labels : label list) =
		match labels with
			| [] -> false
			| l::rem -> 
				(
					match l with 
						| Case _ -> true
						| _ -> false
				) 
	in
	List.filter(
		fun s -> (hasCaseLabel s.labels)
	)cases
	
let getSwitchCaseExpressions (s:stmt) =
	let rec searchLabels (cases:exp list) (labels : label list) =
		match labels with
			| [] -> cases
			| l::rem -> 
				(
					match l with
						| Case(e, _) -> searchLabels (e::cases) rem
						| _ -> searchLabels cases rem
				) 
	in
	List.rev (searchLabels [] s.labels)

let tryGetDefaultCase (cases : stmt list) =
	let rec searchLabels (labels : label list) = 
		match labels with
			| [] -> false
			| l::rem -> 
				(
					match l with
						| Default _ -> true
						| _ -> searchLabels rem
				)
	in 
	try
		Some(List.find(fun s -> searchLabels s.labels)cases)
	with
		| Not_found -> None

let removeFile (out:string) (ext:string) = 
	let files = List.map(fun f -> Filename.concat out f)(Array.to_list (Sys.readdir out)) in
	let rec searchFiles (filelist:string list) = 
		match filelist with
			| [] -> ()
			| f::rem -> 
				if not(Sys.is_directory f) then (
					if endsWith ext f then
						Sys.remove f
				);
				searchFiles rem
	in
	searchFiles files
	
let removeLogFiles (out:string) = 
	removeFile out ".log"
let removeDatFiles (out:string) = 
	removeFile out ".dat"
let removeTxtFiles (out:string) = 
	removeFile out ".txt"
	
let vassert (cond) (msg:string) = 
	if not(cond) then
		Log.vassert msg;
	assert(cond)
		
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
			 
module LvalHashtbl = Hashtbl.Make(
struct
	type t = lval
	let equal lv1 lv2 = (compareLval lv1 lv2)
	let hash lv = Hashtbl.hash (Pretty.sprint 255 (Cil.d_lval()lv))
end)
module ExpHashtbl = Hashtbl.Make(
struct
	type t = exp
	let equal e1 e2 = (compareExp e1 e2)
	let hash e = Hashtbl.hash (Pretty.sprint 255 (Cil.d_exp()e))
end)
