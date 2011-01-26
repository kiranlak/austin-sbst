(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open Printf
open Dominators

let printDominatorTree (fname:string) tree = 
	
	let chan = open_out fname in
	
	let print_edge (src:stmt) (dest:stmt) =
		ignore(fprintf chan "\n\t %d -> %d" src.sid dest.sid)
	in	
	let print_node_label (s : stmt) =
	  let label = 
	  begin
	    match s.skind with
	      | If (e, _, _, _)  -> Printf.sprintf "if(%s)" (Pretty.sprint 255 (Cil.d_exp()e))
	      | Loop _ -> "loop"
	      | Break _ -> "break"
	      | Continue _ -> "continue"
	      | Goto _ -> "goto"
	      | Instr _ -> "instr"
	      | Switch _ -> "switch"
	      | Block _ -> "block"
	      | Return _ -> "return"
	      | TryExcept _ -> "try-except"
	      | TryFinally _ -> "try-finally"
	  end in
	    (Printf.sprintf "%d: %s" s.sid label)
	in
	
	let print_node s = 
		ignore(fprintf chan "%d [label=\"%s\"]" s.sid (print_node_label s))
	in
	let print_tree s = 
		print_node s;
		let doms = children tree s in
		List.iter (print_edge s) doms;
		ignore(fprintf chan "\n")
	in
		
	ignore (fprintf chan "digraph Dominator {\n");
	ignore(domTreeIter print_tree PreOrder tree);
	ignore(fprintf chan  "}\n");
	
	close_out chan;
	
	if (Sys.command ("dot -Tpng "^(fname)^" > "^(Filename.chop_extension fname)^".png")) <> 0 then
			LogManager.error (Printf.sprintf "cannot generate dominator png file for %s.png" (Filename.chop_extension fname));
;;

let trueBranch = 0
let falseBranch = 1

type edge = 
{
	source : stmt;
	index : int; (*for if statements: 0 = false, 1 = true; for switch its the index of the case stmt in case list *)
}
module PS = 
	Set.Make(
		struct 
		type t = edge 
		let compare e1 e2 = 
			if e1.source.sid = e2.source.sid then (
				compare e1.index e2.index
			) else compare e1.source.sid e2.source.sid
		end
)
module IntSet = Set.Make (struct type t = int ;; let compare = compare end)

type cfgnode = 
{
	ns : stmt;
	mutable dependent : PS.t;
}

let controlDependencies : (int, cfgnode) Hashtbl.t = (Hashtbl.create Options.hashtblInitSize)

let reset() = 
	Hashtbl.clear controlDependencies
	
let saveControlDependencies (fileName : string) = 
	let outchan = open_out_bin fileName in
  Marshal.to_channel outchan controlDependencies [];
  close_out outchan

let loadControlDependencies (fileName : string) = 
	Hashtbl.clear controlDependencies;
	let inchan = open_in_bin fileName in
  let ht = (Marshal.from_channel inchan : (int, cfgnode) Hashtbl.t) in
	close_in inchan;
	Hashtbl.iter(
		fun key value -> Hashtbl.add controlDependencies key value
	)ht
	
let makeEdge (source:stmt) (index:int) = 
	{source=source;index=index}

let containsStmt (id:int) (dependent:PS.t) = 
		PS.exists(
			fun edge -> edge.source.sid = id
		)dependent
		
let reverseCFG (stmts:stmt list) = 
	List.map(
		fun s ->
		let oldsuccs = s.succs in
		s.succs <- s.preds;
		s.preds <- oldsuccs;
		s
	)stmts
	
let computePIDOMandTree (f:fundec) = 
	assert((List.length f.sbody.bstmts) > 0);
	
	let all_s, sink_s = Dataflow.find_stmts f in
	
	f.sallstmts <- (reverseCFG f.sallstmts);
		
	let v_end = Cil.mkEmptyStmt () in
	
	List.iter(
		fun s -> 
			s.preds <- (s.preds @ [v_end]);
			v_end.succs <- (v_end.succs @ [s]);
	)sink_s;
	
	f.sbody.bstmts <- (v_end::f.sbody.bstmts);
	
	let ipdom,postDomTree = Dominators.computeDomTree ~doCFG:false f in
	
	f.sallstmts <- (reverseCFG f.sallstmts);
	f.sbody.bstmts <- (List.tl f.sbody.bstmts);
	
	List.iter(
		fun s -> s.succs <- []
	)sink_s; 
	
	(ipdom, postDomTree)

let getPostDominator ipdom (s:stmt) = 
	try
		Inthash.find ipdom s.sid
	with
		| Not_found -> None

let isBranchingStmt (s:stmt) = 
	match s.skind with
		| If _ | Switch _  -> true
		| _ -> false

let addControlDependency (edg:edge) (s:stmt) = 
	let edgeDependent = 
		if (Hashtbl.mem controlDependencies edg.source.sid) then (
			(Hashtbl.find controlDependencies edg.source.sid).dependent
		) else
			PS.empty
	in
	let existing = 
		if (Hashtbl.mem controlDependencies s.sid) then
			(Hashtbl.find controlDependencies s.sid).dependent
		else
			PS.empty
	in
	let dependent = PS.union edgeDependent (PS.union existing (PS.singleton edg)) in
	let node = {ns=s;dependent=dependent} in
	Hashtbl.replace controlDependencies s.sid node

		
let computeControlDependencies (source : file) (target:fundec) = 

	Hashtbl.clear controlDependencies;
	
	let info, tree = computePIDOMandTree target in
	
	(*Nodes control dependent on edge (u->v) are nodes on path up the postdominator tree *)
	(*from v to ipdom(u), excluding ipdom(u)*)
	
	let rec computeCDNodes (stopId:int) (current:stmt) (edg:edge) = 
		if current.sid <> stopId then (
			addControlDependency edg current;
			let ipdom = getPostDominator info current in
			match ipdom with
				| None -> ()
				| Some(s) -> computeCDNodes stopId s edg
		)
	in
	List.iter(
		fun s -> 
			let stopStmt = getPostDominator info s in
			let stopId = match stopStmt with
				| None -> -1
				| Some(s') -> s'.sid
			in
			match s.skind with
			| If(e, thn, el, _) -> 
				if List.length s.succs > 0 then
					computeCDNodes stopId (List.hd s.succs) (makeEdge s trueBranch);
				if List.length s.succs > 1 then
					computeCDNodes stopId (List.hd (List.tl s.succs)) (makeEdge s falseBranch);
			| Switch(e,blk,csl,_) ->
				(* assume: successors are case labels in order *)
				let counter = ref 0 in
				List.iter(
					fun s' -> 
						computeCDNodes stopId s' (makeEdge s !counter);
						incr counter
				)s.succs 
			| _ -> ()
	)target.sallstmts

let getDependentNodes (sid : int) = 
	(**TODO: I will ignore all node ids where elt.source.sid > sid. Essentially this ignores dependencies from back edges. 
			     Check that this is ok. Otherwise return full *)
	let full = if Hashtbl.mem controlDependencies sid then
		(Hashtbl.find controlDependencies sid).dependent
	else
		PS.empty
	in
	PS.filter(fun elt -> elt.source.sid <= sid)full
		
let filterUniqueStmts (dependent : PS.t) = 
	PS.fold(
		fun elt (filtered,removedIds) -> 
			let isUnique = 
				(PS.cardinal (PS.filter(
					fun elt' -> elt'.source.sid = elt.source.sid
				)dependent)) = 1
			in
			if isUnique then
				((PS.add elt filtered), removedIds)
			else
				(filtered, (IntSet.add elt.source.sid removedIds))
	) dependent (PS.empty, IntSet.empty)

let getCriticalEdges (sid:int) = 
	let edges = getDependentNodes sid in
	PS.fold (
		fun el res -> 
			((el.source.sid, el.index)::res)
	) edges []

let getCriticalEdgesOfCurrentStmt (sid:int) (targetDependent:PS.t) = 
	PS.fold(
		fun el res -> 
			if el.source.sid = sid then (el.index::res)
			else res
	)targetDependent []
	
let getDependentNodesAndEdges (sid:int) = 
	let dependent =  getDependentNodes sid in
	let uniqueElements,removedIds = filterUniqueStmts dependent in
	let cnt = (PS.cardinal uniqueElements) + (IntSet.cardinal removedIds) in
	let edgesOfCurrentNode = PS.fold(
			fun el res -> if el.source.sid = sid then (el.index::res) else res
			) dependent []
	in
	(cnt,dependent, edgesOfCurrentNode)

let computeWegenerApproachLevel (targetCnt:int) (targetDependent:PS.t) (sid:int) = 
	if not(PS.exists(fun el -> el.source.sid = sid)targetDependent) then (
		(false, 0, [])
	) else (
		let cnt,dependent,edges = getDependentNodesAndEdges sid in
		if cnt > targetCnt then (
			LogManager.error (Printf.sprintf "cnt > targetCnt, (%d > %d, sid=%d)\n"
				cnt targetCnt sid);
		);
		let _cnt = (targetCnt - cnt) in
		(true,_cnt, edges)	
	)

class branchCounter (branchCount : int ref) (ids: (int*int) list ref) = object(self)
	inherit nopCilVisitor
	
	method vstmt (s:stmt) = 
		(match s.skind with
			| If _ -> 
				branchCount := !branchCount + 2;
				ids := ((s.sid, 2)::(!ids))
			| Switch(_, _, csl, _) ->
				let indxCnt = (List.length csl) in 
				branchCount := !branchCount + indxCnt;
				ids := ((s.sid, indxCnt)::(!ids))
			| _ -> ());
		DoChildren
	
	method vfunc (f:fundec) = 
		if startsWith "Austin__" f.svar.vname || f.svar.vname = "main" then SkipChildren
		else DoChildren
end

let countFundecBranches (f:fundec) = 
	let count = ref 0 in
	let ids = ref [] in
	let vis = new branchCounter count ids in
	ignore(visitCilFunction vis f);
	(!count,!ids)

let countFileBranches (source:file) = 
	let count = ref 0 in
	let ids = ref [] in
	let vis = new branchCounter count ids in
	ignore(visitCilFileSameGlobals vis source);
	!count
;;