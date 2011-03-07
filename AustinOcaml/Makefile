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

#OCAMLOPT=/usr/local/bin/ocamlopt
OCAMLOPT=ocamlopt
OCAMLDEP=ocamldep
INCLUDES=-I ${CILOBJ} -I log/ -I programstructure/ -I testcases/ \
-I searchMethods/ -I random/ -I solution/ -I symbolic/ -I execution/ -I utils/ \
-I instrumentation/ -I config/ -I ui/ -I searchMethods/objectives/ -I solution/generator/ \
-I testsuite/

OCAMLOPTFLAGS=$(INCLUDES) # add other options for ocamlopt here

SOURCES=config/configFile.ml options.ml log/logManager.ml \
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

COMMON_OBJS=str.cmxa unix.cmxa nums.cmxa cil.cmxa
AUSTIN_OBJS=${SOURCES:%.ml=%.cmx}

TESTRUNNER_OBJS=$(subst ui/commandLineHandler.cmx,,${SOURCES:%.ml=%.cmx}) testsuite/testSuiteRunner.cmx

# Common rules
.SUFFIXES: .ml .mli .cmo .cmi .cmx

.mli.cmi:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<
        
#%.cmx %.mli: %.ml
#	${OCAMLOPT} -o $@ ${OCAMLOPTFLAGS} -c $<

${EXE} : ${AUSTIN_OBJS}
	$(OCAMLOPT) -o ${EXE} $(OCAMLOPTFLAGS) $(COMMON_OBJS) $(AUSTIN_OBJS)

${TESTEXE} : ${TESTRUNNER_OBJS}
	$(OCAMLOPT) -o ${TESTEXE} $(OCAMLOPTFLAGS) -I testsuite/ $(COMMON_OBJS) ${TESTRUNNER_OBJS} 

#instrumentation/instrument.cmx ui/commandLineHandler.cmx testsuite/testSuiteRunner.cmx: instrumentation/preconditionAnalyser.cmx instrumentation/preconditionAnalyser.mli
#solution/generator/solutionGenerator.cmx : solution/generator/preconditions.cmx
#searchMethods/symbolicHillClimbSearch.cmx searchMethods/hillClimbSearch.cmx searchMethods/randomSearch.cmx execution/execute.cmx: solution/generator/solutionGenerator.cmx
	
all : ${EXE} ${TESTEXE}
	
clean:
	-rm -f ${EXE} 
	-rm -f ${TESTEXE}
	-rm -f ${SOURCES:%.ml=%.cmx} ${SOURCES:%.ml=%.cmi} ${SOURCES:%.ml=%.o}
	-rm -f testsuite/testSuiteRunner.cmi testsuite/testSuiteRunner.cmx testsuite/testSuiteRunner.o
