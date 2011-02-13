ACAMLDIR := ../AustinOcaml/

ifdef BYTE
OCC := ocamlc
EXE := ../austin.byte
else
OCC := ocamlopt
EXE := ../austin.bin
endif

OCCFLAGS := -I ${CILOBJ} -I ${ACAMLDIR} -I ${ACAMLDIR}log/ -I ${ACAMLDIR}programstructure/ -I ${ACAMLDIR}testcases/ -I ${ACAMLDIR}searchMethods/ -I ${ACAMLDIR}random/ -I ${ACAMLDIR}solution/ -I ${ACAMLDIR}symbolic/ -I ${ACAMLDIR}execution/ -I ${ACAMLDIR}utils/ -I ${ACAMLDIR}instrumentation/ -I ${ACAMLDIR}config/ -I ${ACAMLDIR}ui/ -I ${ACAMLDIR}searchMethods/objectives/ -I ${ACAMLDIR}solution/generator/

OCAMLSOURCES := ${ACAMLDIR}config/configFile.ml ${ACAMLDIR}options.ml ${ACAMLDIR}log/logManager.ml ${ACAMLDIR}searchMethods/objectives/baseObjValue.ml ${ACAMLDIR}utils/utils.ml ${ACAMLDIR}solution/solution.ml ${ACAMLDIR}searchMethods/objectives/baseObjFunc.ml ${ACAMLDIR}programstructure/cfginfo.ml ${ACAMLDIR}searchMethods/baseSearchMethod.ml ${ACAMLDIR}symbolic/symbolic.ml ${ACAMLDIR}random/austinRand.ml ${ACAMLDIR}testcases/testCaseWriter.ml ${ACAMLDIR}symbolic/equivalenceGraph.ml ${ACAMLDIR}solution/generator/solutionGenerator.ml ${ACAMLDIR}searchMethods/objectives/branchCoverageObjFunc.ml ${ACAMLDIR}searchMethods/hillClimbSearch.ml ${ACAMLDIR}searchMethods/randomSearch.ml ${ACAMLDIR}instrumentation/traceManager.ml ${ACAMLDIR}instrumentation/branchtrace.ml ${ACAMLDIR}instrumentation/preprocessor.ml ${ACAMLDIR}instrumentation/symbolictrace.ml ${ACAMLDIR}instrumentation/testdriver.ml ${ACAMLDIR}execution/execute.ml ${ACAMLDIR}instrumentation/instrument.ml ${ACAMLDIR}ui/commandLineHandler.ml

OCAMLOBJECTS := ${OCAMLSOURCES:%.ml=%.cmx}
OCAMLO := ${OCAMLSOURCES:%.ml=%.o}
OCAMLCMI := ${OCAMLSOURCES:%.ml=%.cmi}

%.cmx : %.ml
	${OCC} -o $@ ${OCCFLAGS} -c $<
	
${EXE} : ${OCAMLOBJECTS}
	${OCC} ${OCCFLAGS} str.cmxa unix.cmxa nums.cmxa cil.cmxa ${OCAMLOBJECTS} -o ${EXE} 
	
bin : ${EXE}
	
clean:
	-rm -f ${OCAMLOBJECTS}
	-rm -f ${OCAMLO} 
	-rm -f ${OCAMLCMI}
	
