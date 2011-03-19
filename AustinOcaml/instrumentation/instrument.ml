(* Copyright: Kiran Lakhotia, University College London, 2011 *)
open Cil
open Printf
open Options
open Utils
open Preconditions
open CheckUnsupportedFeatures
	
module Log = LogManager

let insOptFutName = ref ""
let insOptRecursive = ref false
let insOptPPFiles = ref false
let insOptMergedName = ref ""
let insOptPrintFuncs = ref false
let insOptPrintGlobs = ref false
		
let marshalFundec (source : file) (f : fundec) (fileName : string) = 
	let outchan = open_out_bin fileName in
  Marshal.to_channel outchan f [];
  close_out outchan
			
let addTraceInstrumentation (source:file) (f:fundec) (testDriverFuncNames:string list) (traces:string list) = 
	let symprotos,symPostDrv = 
		if (List.mem "symbolic" traces) then (
			Log.log "\nAdding symbolic trace\n";
			Symbolictrace.main source testDriverFuncNames;
		) else
			[],[] 
	in
	let branchprotos,branchPostDrv = 
		if (List.mem "branch" traces) then (
			Log.log "\nAdding branch trace\n";
			Branchtrace.main source f testDriverFuncNames
		) else
			[],[] 
	in
	TraceManager.insertInstructions source;
	let protos = (symprotos @ branchprotos) in
	let postInstr = (symPostDrv @ branchPostDrv) in
	List.iter(
		fun fdec -> 
			fdec.svar.vstorage <- Extern;
			source.globals <- (GVarDecl(fdec.svar, locUnknown)::source.globals)
	) protos;
	postInstr

class insertPostDrvInstrVis (ilist:instr list) = object(this)
	inherit nopCilVisitor
	val mutable currentFunc = ""
	
	method vfunc (f:fundec) = currentFunc <- f.svar.vname; DoChildren
	method vinst (i:instr) = 
		match i with
			| Call(_, f, _, _) when currentFunc = "main" -> 
				let fname = Pretty.sprint 255 (Cil.d_exp()f) in
				if fname = "Austin__Teardown" then (
					ChangeTo (ilist@[i])
				) else
					DoChildren
			| _ -> DoChildren
end

let addPostDrvInstr (source:file) (ins:instr list) = 
	let vis = new insertPostDrvInstrVis ins in
	visitCilFileSameGlobals vis source
	
let saveSourceToFile (f:file) (out:string) = 
	Log.log "Saving source to file...";
	(*print_CIL_Input := true;*)
	lineDirectiveStyle := Some(LineCommentSparse);
	let ochan = open_out out in
	dumpFile defaultCilPrinter ochan out f;
	close_out ochan;
	Log.log "done\n"
			
class insertFUTSetupCall (ins:instr list) = object(this)
	inherit nopCilVisitor
	method vinst (i:instr) = 
		match i with
			| Call(_,f,_,_) -> 
				(
					match f with
						| Lval(l) -> (
								match l with
									| Var v, _ -> (
											if v.vname = "Austin__drv" then (
												this#queueInstr ins
											);
											SkipChildren
										)
									| _ -> SkipChildren
							)
						| _ -> SkipChildren
				)
			| _ -> SkipChildren
end	
let parseAndMergeSources (sources : string list) = 
	let csources = List.filter(fun f -> (endsWith ".c" f))sources in
	let isources = List.filter(fun f -> (endsWith ".i" f))sources in
	let regDotC = Str.regexp_string ".c" in
	let toInstrument = 
		if (List.length csources) > 0 && !insOptPPFiles then (
			let compiler = ConfigFile.find Options.keyCompiler in
			let includes = ConfigFile.find Options.keyCompilerIncl in
			let ppOptions = ConfigFile.find Options.keyCompilerOpts in
			((List.map(
				fun f -> 
					Log.log (Printf.sprintf "Executing preprocessor command: %s\n" (compiler^" "^includes^" "^ppOptions^" "^f));
					let outfile = Str.global_replace regDotC ".i" f in
					if (Sys.command (compiler^" -o "^outfile^" "^includes^" "^ppOptions^" "^f)) <> 0 then (
						Log.error (Printf.sprintf "Error while preprocessing %s file\n" f)
					);
					outfile
			)csources) @ isources)				
		) else
			(csources @ isources)
	in
	Mergecil.merge (List.map (fun a -> Frontc.parse a ()) toInstrument) "sutMerged.c"
	
let mainInstrument (sources : string list) = 
	
	let criterion = ConfigFile.find Options.keyTDGCriterion in
	let search = ConfigFile.find Options.keyTDGMethod in
	let traces = ref [] in
	if criterion = "branch" then
		traces := ("branch"::!traces)
	else
		Log.error (Printf.sprintf "Unrecognized tdgCriterion:%s\n" criterion);
	
	if search = "chc" then (
		traces := ("symbolic"::!traces);
		Preprocessor.addExplicitReturnStmt := true;
	);
	
	let sutSource = parseAndMergeSources sources in
	
	if hasUnsupportedFeature sutSource then
		Log.error "The source file(s) contains unsupported features and cannot be tested by Austin\n";
	
	let austinPreamble = Frontc.parse (ConfigFile.find Options.keySUTpreamble) () in
		
	Log.log "Preprocessing...";
	Preprocessor.removeUnsafeCode sutSource;
	Preprocessor.removeRegisterStorage sutSource;
	Preprocessor.renameMain sutSource.globals;
	Preprocessor.convertInstrToStmt sutSource;
	Preprocessor.insertExplicitReturnStatement sutSource;
	Log.log "done\n";
	
	match (tryFindFundecFromName sutSource !insOptFutName) with
		| None -> 
			Log.error (sprintf "Could not find function under test named %s\r\n" !insOptFutName)
		| Some(f) -> (
			
				Log.log "Clearing old log files...";
				removeLogFiles !Options.austinOutDir;
				removeDatFiles !Options.austinOutDir;
				Log.log "done\n";
									
				Log.log "Generating test driver...\n";
				let drv = Testdriver.createTestDriver f sutSource in
				let testDriverFuncNames = Testdriver.addAustinFunctions sutSource in
				Log.log "Done test driver\n";
				
				Log.log "Adding function prototypes...";
				sutSource.globals <- ((!Testdriver.globalVariables) @ sutSource.globals);
				Log.log "done\n";
				
				Log.log "Clearing CFG info...";
				Cfg.clearFileCFG sutSource;
				Log.log "done\n";
				
				Log.log "Computing CFG info...";
	  		Cfg.computeFileCFG sutSource;
				Log.log "done\n";
				
				Log.log "Saving source (binary)...";
				marshalSource sutSource (ConfigFile.find Options.keyBinInstrumentedSrouce);
				Log.log "done\n";
				
				Log.log "Saving fut fundec (binary)...";
				marshalFundec sutSource f (ConfigFile.find Options.keyFutFundec);
				Log.log "done\n";
				
				Log.log "Saving test driver fundec (binary)...";
				marshalFundec sutSource drv (ConfigFile.find Options.keyDrvFundec);
				Log.log "done\n";
				
				Log.log "Saving any preconditions (binary)...";
				collectPreconditions sutSource f;
				Log.log "done\n";
				
				Log.log "Adding trace instrumentations...";
				let postDrvInstr = addTraceInstrumentation sutSource f testDriverFuncNames !traces in
															
				Log.log "Adding AUSTIN globals...";
				let source = Mergecil.merge [austinPreamble;sutSource] "merged.c" in
				Log.log "done\n";
				
				Log.log "Adding post Austin__drv() instructions...";
				addPostDrvInstr source postDrvInstr;
				Log.log "done\n";
				
				Log.log "Removing unused declarations...";
				Rmtmps.removeUnusedTemps source;
				Log.log "done\n";
				
				(* add SymexTestDriver *)
				saveSourceToFile source (ConfigFile.find Options.keyInstrumentedSource)
			)
;;