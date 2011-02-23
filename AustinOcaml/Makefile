OS := $(shell uname)

ifeq ($(OS),Linux)
OS := LINUX
endif

# SET THIS TO CIL DIRECTORY
ifndef CILHOME
ifeq ($(OS),Darwin)
CILHOME := /Users/kiran/workspace/cil-1.3.7/
else 
ifeq ($(OS),LINUX)
CILHOME := /home/kiran/workspace/cil-1.3.7/
endif
endif
endif

CILOBJ := ${CILHOME}obj/x86_${OS}/

###############################
TESTEXE := testRunner
EXE := austin
OCC := ocamlopt
#OCC := /usr/local/bin/ocamlopt

OCAMLINCL := -I ${CILOBJ} -I log/ -I programstructure/ -I testcases/ \
-I searchMethods/ -I random/ -I solution/ -I symbolic/ -I execution/ -I utils/ \
-I instrumentation/ -I config/ -I ui/ -I searchMethods/objectives/ -I solution/generator/ \
-I testsuite/

MLSRCS := config/configFile.ml options.ml log/logManager.ml \
searchMethods/objectives/baseObjValue.ml utils/utils.ml solution/solution.ml \
searchMethods/objectives/baseObjFunc.ml programstructure/cfginfo.ml \
searchMethods/baseSearchMethod.ml symbolic/symbolic.ml random/austinRand.ml \
testcases/testCaseWriter.ml symbolic/equivalenceGraph.ml solution/generator/preconditions.ml \
solution/generator/solutionGenerator.ml searchMethods/objectives/branchCoverageObjFunc.ml \
searchMethods/symbolicHillClimbSearch.ml searchMethods/hillClimbSearch.ml searchMethods/randomSearch.ml \
instrumentation/traceManager.ml instrumentation/branchtrace.ml \
instrumentation/preprocessor.ml instrumentation/preconditionAnalyser.ml instrumentation/symbolictrace.ml \
instrumentation/testdriver.ml execution/execute.ml instrumentation/instrument.ml \
ui/commandLineHandler.ml

OCAMLSRCS := ${MLSRCS:%.ml=%.mli}
OCAMLOBJS := ${MLSRCS:%.ml=%.cmx}

TESTOBJS := $(subst ui/commandLineHandler.cmx,,${OCAMLOBJS})

%.cmx %.mli: %.ml
	${OCC} -o $@ ${OCAMLINCL} -c $<

${EXE} : ${OCAMLOBJS}
	${OCC} -o ${EXE} ${OCAMLINCL} str.cmxa unix.cmxa nums.cmxa cil.cmxa ${OCAMLOBJS} 

	
${TESTEXE} : ${TESTOBJS} testsuite/testSuiteRunner.cmx
	${OCC} ${OCAMLINCL} str.cmxa unix.cmxa nums.cmxa cil.cmxa ${TESTOBJS} testsuite/testSuiteRunner.cmx -o ${TESTEXE}
	
all : ${EXE} ${TESTEXE}
	
clean:
	-rm -f ${EXE} 
	-rm -f ${TESTEXE}
	-rm -f ${OCAMLOBJS} ${MLSRCS:%.ml=%.cmi} ${MLSRCS:%.ml=%.o}
	-rm -f testsuite/testSuiteRunner.cmi testsuite/testSuiteRunner.cmx testsuite/testSuiteRunner.o
