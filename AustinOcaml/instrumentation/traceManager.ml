(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil

let htToInsert : (int, instr list) Hashtbl.t = Hashtbl.create 100
let htToAppend : (int, instr list) Hashtbl.t = Hashtbl.create 50

module Log = LogManager

let newSid = ref (-2)

let reset() = 
	Hashtbl.clear htToInsert;
	Hashtbl.clear htToAppend;
	newSid := (-2)
			 
let pushInstrBeforeStmt (s:stmt) (ilist:instr list) = 
	let existing = 
		try
			Hashtbl.find htToInsert s.sid
		with
			| Not_found -> []
	in
	Hashtbl.replace htToInsert s.sid (ilist@existing)
	
let appendInstr (s:stmt) (ilist:instr list) = 
	let existing = 
		try
			Hashtbl.find htToAppend s.sid
		with
			| Not_found -> []
	in
	Hashtbl.replace htToAppend s.sid (ilist@existing)
	
let addInstrsToBlock (b:block) (ilist:instr list) = 
	match b.bstmts with
		| [] -> (
				let s' = mkStmt (Instr(ilist)) in
				s'.sid <- !newSid;
				decr newSid;
				b.bstmts <- [s']
			)
		| s::rem -> (
				let existing = 
					try
						Hashtbl.find htToInsert s.sid
					with
						| Not_found -> []
				in
				Hashtbl.replace htToInsert s.sid (ilist@existing)
			)
			
class insertInstructionsVis = object(this)
	inherit nopCilVisitor
	
	method vstmt (s:stmt) = 
		if Hashtbl.mem htToInsert s.sid then (
			let existing = Hashtbl.find htToInsert s.sid in
			ChangeDoChildrenPost(s, (fun s' -> this#queueInstr existing; s'))
		) else if Hashtbl.mem htToAppend s.sid then (
			let existing = 
				List.map(fun i -> mkStmtOneInstr i)(Hashtbl.find htToAppend s.sid) 
			in
			ChangeDoChildrenPost(s, (
				fun s' ->  
					let skind' = Block(mkBlock (compactStmts (s'::(existing)))) in
					s'.skind <- skind';
					s'))
		) else
			DoChildren
end
let insertInstructions (source:file) = 
	let vis = new insertInstructionsVis in
	visitCilFileSameGlobals vis source;