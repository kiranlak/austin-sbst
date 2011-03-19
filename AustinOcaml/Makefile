OS=$(shell uname)

ifeq ($(OS),Linux)
OS=LINUX
endif

# SET THIS TO CIL DIRECTORY
ifndef CILHOME
ifeq ($(OS),Darwin)
CILHOME=/Users/kiran/workspace/cil-1.3.7/
else 
ifeq ($(OS),LINUX)
CILHOME=/home/kiran/workspace/cil-1.3.7/
endif
endif
endif

CILOBJ=$(CILHOME)obj/x86_$(OS)/

###############################
TESTEXE=testSuiteRunner
EXE=austin

OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLDEP=ocamldep

INCLUDES=-I $(CILOBJ) -I log/ -I programstructure/ -I testcases/ \
-I searchMethods/ -I random/ -I solution/ -I symbolic/ -I execution/ -I utils/ \
-I instrumentation/ -I config/ -I ui/ -I searchMethods/objectives/ -I solution/generator/ \
-I testsuite/

OCAMLOPTFLAGS=$(INCLUDES) # add other options for ocamlopt here

SOURCES=config/configFile.ml options.ml log/logManager.ml \
searchMethods/objectives/baseObjValue.ml utils/utils.ml solution/solution.ml \
searchMethods/objectives/baseObjFunc.ml programstructure/cfginfo.ml \
searchMethods/baseSearchMethod.ml symbolic/symbolic.ml random/austinRand.ml \
testcases/testCaseWriter.ml symbolic/equivalenceGraph.ml solution/generator/arrayInputs.ml \
solution/generator/preconditions.ml solution/generator/solutionGenerator.ml \
searchMethods/objectives/branchCoverageObjFunc.ml \
searchMethods/symbolicHillClimbSearch.ml searchMethods/hillClimbSearch.ml searchMethods/randomSearch.ml \
instrumentation/traceManager.ml instrumentation/branchtrace.ml \
instrumentation/checkUnsupportedFeatures.ml instrumentation/preprocessor.ml \
instrumentation/symbolictrace.ml instrumentation/testdriver.ml execution/execute.ml \
instrumentation/instrument.ml ui/commandLineHandler.ml

AUSTIN_CINT=$(SOURCES:%.ml=%.cmi)

COMMON_OBJS=str.cmxa unix.cmxa nums.cmxa cil.cmxa
AUSTIN_OBJS=$(SOURCES:%.ml=%.cmx)

TESTRUNNER_SOURCES=testsuite/testSuiteRunner.ml
TESTRUNNER_CINT=$(TESTRUNNER_SOURCES:%.ml=%.cmi)
TESTRUNNER_OBJS=$(subst ui/commandLineHandler.cmx,,$(SOURCES:%.ml=%.cmx)) $(TESTRUNNER_SOURCES:%.ml=%.cmx)
 
# Common rules
.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	$(OCAMLC) $(OCAMLOPTFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(OCAMLOPTFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

$(EXE) : $(AUSTIN_OBJS)
	$(OCAMLOPT) -o $(EXE) $(OCAMLOPTFLAGS) $(COMMON_OBJS) $(AUSTIN_OBJS)

$(TESTEXE) : $(TESTRUNNER_OBJS)
	$(OCAMLOPT) -o $(TESTEXE) $(OCAMLOPTFLAGS) $(COMMON_OBJS) $(TESTRUNNER_OBJS) 

all : $(EXE) $(TESTEXE)
	
clean:
	-rm -f $(EXE) 
	-rm -f $(TESTEXE)
	-rm -f $(SOURCES:%.ml=%.cmx) $(SOURCES:%.ml=%.cmi) $(SOURCES:%.ml=%.o) $(SOURCES:%.ml=%.cmo)
	-rm -f $(TESTRUNNER_SOURCES:%.ml=%.cmx) $(TESTRUNNER_SOURCES:%.ml=%.cmi) $(TESTRUNNER_SOURCES:%.ml=%.o) $(TESTRUNNER_SOURCES:%.ml=%.cmo)

# Dependencies
.depend:$(SOURCES) $(TESTRUNNER_SOURCES)
	$(OCAMLDEP) $(INCLUDES) $(SOURCES) $(AUSTIN_CINT) $(TESTRUNNER_SOURCES) $(TESTRUNNER_CINT) > .depend

include .depend
