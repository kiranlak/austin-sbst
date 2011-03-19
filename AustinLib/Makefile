OS=$(shell uname)

ifeq ($(OS),Linux)
OS=LINUX
endif

#ARCH=$(subst architecture:,,$(shell ocamlopt -config | grep architecture: ))
ARCH=$(shell arch)

# SET THIS TO CIL DIRECTORY
ifndef CILHOME
ifeq ($(OS),Darwin)
CIL=/Users/kiran/workspace/cil-1.3.7/
else ifeq ($(OS),LINUX)
CIL=/home/kiran/workspace/cil-1.3.7/
endif
else
CIL=$(CILHOME)
endif

CILOBJ=$(CIL)obj/x86_$(OS)/


###############################
OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLDEP=ocamldep

CC=g++

CPPDIR=src/
AustinOcaml_DIR=../AustinOcaml/

LIBNAME=libAustinLib.a

OCAMLINCLUDES=-I $(CILOBJ) -I $(AustinOcaml_DIR) -I $(AustinOcaml_DIR)config/ \
-I $(AustinOcaml_DIR)log/ -I $(AustinOcaml_DIR)utils/ -I $(AustinOcaml_DIR)symbolic/ \
-I $(AustinOcaml_DIR)searchMethods/objectives/ -I $(AustinOcaml_DIR)solution/ \
-I $(AustinOcaml_DIR)lib/

OCAMLOPTFLAGS=$(OCAMLINCLUDES) # add other options for ocamlopt here

CXXFLAGS=-O0 -g3 -Wall -fmessage-length=0 -fPIC

ifeq ($(OS),Darwin)
OCAMLLIB=/usr/local/lib/ocaml/
CXXFLAGS += -arch $(ARCH) -I $(OCAMLLIB)
else
ifeq ($(OS),LINUX)
OCAMLLIB=/usr/lib/ocaml/
CXXFLAGS += -I $(OCAMLLIB)
endif
endif

OCAMLSOURCES=$(AustinOcaml_DIR)config/configFile.ml $(AustinOcaml_DIR)options.ml \
$(AustinOcaml_DIR)log/logManager.ml $(AustinOcaml_DIR)utils/utils.ml \
$(AustinOcaml_DIR)symbolic/symbolic.ml $(AustinOcaml_DIR)searchMethods/objectives/baseObjValue.ml \
$(AustinOcaml_DIR)solution/solution.ml $(AustinOcaml_DIR)lib/mainLib.ml \
$(AustinOcaml_DIR)lib/symtrace.ml $(AustinOcaml_DIR)lib/solutionManager.ml

OCAML_CINT=${OCAMLSOURCES:%.ml=%.cmi}

COMMON_OBJS=str.cmxa unix.cmxa cil.cmxa
OCAML_OBJS=$(OCAMLSOURCES:%.ml=%.cmx)

CPPSRCS=$(CPPDIR)traces/BranchDistanceTrace.cpp $(CPPDIR)traces/SymbolicTrace.cpp \
$(CPPDIR)traces/Trace.cpp $(CPPDIR)sut.cpp $(CPPDIR)TraceManager.cpp

CPPHEADER=$(CPPSRCS:%.cpp=%.h)
CPPOBJS := $(CPPSRCS:%.cpp=%.o)

ifdef THIN
LIBOBJS := $(CPPOBJS) obj/camlcode.o
else
LIBOBJS := $(CPPOBJS) obj/camlcode.o extlib/libasmrun/*.o extlib/libperfcount/*.o extlib/libstr/*.o extlib/libunix/*.o
endif

# Common rules
.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	$(OCAMLC) $(OCAMLOPTFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(OCAMLOPTFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

obj/camlcode.o : $(OCAML_OBJS)
	$(OCAMLOPT) -output-obj -o obj/camlcode.o $(OCAMLOPTFLAGS) $(COMMON_OBJS) $(OCAML_OBJS)
		
%.o : %.cpp
	$(CC) -o $@ -c $(CXXFLAGS) $<

extlib/libasmrun/*.o : 
	cd extlib/libasmrun/; \
	ar -x $(OCAMLLIB)libasmrun.a
	 
asmrun : extlib/libasmrun/*.o

extlib/libunix/%.o : 
	cd extlib/libunix/; \
	ar -x $(OCAMLLIB)libunix.a
	
unix : extlib/libunix/%.o

extlib/libstr/%.o : 
	cd extlib/libstr/; \
	ar -x $(OCAMLLIB)libstr.a
	
str : extlib/libstr/%.o

extlib/libperfcount/%.o : 
	cd extlib/libperfcount/; \
	ar -x $(CILOBJ)libperfcount.a
	
perfcount : extlib/libperfcount/%.o

$(LIBNAME) : $(LIBOBJS)
	ar -r "$(LIBNAME)" $(LIBOBJS)
	
all : $(LIBNAME)
	
clean:
	-rm -f $(LIBNAME) 
	-rm -f $(CPPDIR)*.o
	-rm -f $(CPPDIR)traces/*.o
	-rm -f obj/camlcode.o
	-rm -f $(OCAML_OBJS) $(OCAMLSOURCES:%.ml=%.cmi) $(OCAMLSOURCES:%.ml=%.o) $(OCAMLSOURCES:%.ml=%.cmo)
#	-rm -f ${ALIBDIR}extlib/libasmrun/*.o 
#	-rm -f ${ALIBDIR}extlib/libperfcount/*.o 
#	-rm -f ${ALIBDIR}extlib/libstr/*.o 
#	-rm -f ${ALIBDIR}extlib/libunix/*.o

# Dependencies
.depend:$(OCAMLSOURCES)
	$(OCAMLDEP) $(OCAMLINCLUDES) $(OCAMLSOURCES) $(OCAML_CINT) > .depend

include .depend
