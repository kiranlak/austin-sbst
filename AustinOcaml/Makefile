OS := $(shell uname)

ifeq ($(OS),Linux)
OS := LINUX
endif

OCAMLARCH=$(subst architecture:,,$(shell ocamlopt -config | grep architecture: ))

# SET THIS TO CIL DIRECTORY
ifndef CILHOME
ifeq ($(OS),Darwin)
CIL := /Users/kiran/workspace/cil-1.3.7/
else ifeq ($(OS),LINUX)
CIL := /home/kiran/workspace/cil-1.3.7/
endif
else
CIL := ${CILHOME}
endif

CILOBJ := ${CIL}obj/x86_${OS}/

###############################

EXE := austin
OCC := ocamlopt


OCAMLINCL := -I ${CILOBJ} -I . -I log/ -I programstructure/ -I testcases/ \
-I searchMethods/ -I random/ -I solution/ -I symbolic/ -I execution/ -I utils/ \
-I instrumentation/ -I config/ -I ui/ -I searchMethods/objectives/ -I solution/generator/

OCAMLSRCS := config/configFile.ml options.ml log/logManager.ml \
searchMethods/objectives/baseObjValue.ml utils/utils.ml solution/solution.ml \
searchMethods/objectives/baseObjFunc.ml programstructure/cfginfo.ml \
searchMethods/baseSearchMethod.ml symbolic/symbolic.ml random/austinRand.ml \
testcases/testCaseWriter.ml symbolic/equivalenceGraph.ml \
solution/generator/solutionGenerator.ml searchMethods/objectives/branchCoverageObjFunc.ml \
searchMethods/symbolicHillClimbSearch.ml searchMethods/hillClimbSearch.ml searchMethods/randomSearch.ml \
instrumentation/traceManager.ml instrumentation/branchtrace.ml \
instrumentation/preprocessor.ml instrumentation/symbolictrace.ml \
instrumentation/testdriver.ml execution/execute.ml instrumentation/instrument.ml \
ui/commandLineHandler.ml

OCAMLOBJS := ${OCAMLSRCS:%.ml=%.cmx}

%.cmx : %.ml
	${OCC} -o $@ ${OCAMLINCL} -c $<
	
${EXE} : ${OCAMLOBJS}
	${OCC} ${OCAMLINCL} str.cmxa unix.cmxa nums.cmxa cil.cmxa ${OCAMLOBJS} -o ${EXE} 
	
all : ${EXE}
	
clean:
	-rm -f ${EXE}
	-rm -f ${OCAMLOBJS} ${OCAMLSRCS:%.ml=%.cmi} ${OCAMLSRCS:%.ml=%.o}

