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
OCC := ocamlopt
CC := g++

CPPDIR := src/
OCAMLDIR := ../AustinOcaml/

LIBNAME := libAustinLib.a

OCAMLINCL := -I ${CILOBJ} -I ${OCAMLDIR} -I ${OCAMLDIR}config/ \
-I ${OCAMLDIR}log/ -I ${OCAMLDIR}utils/ -I ${OCAMLDIR}symbolic/ \
-I ${OCAMLDIR}searchMethods/objectives/ -I ${OCAMLDIR}solution/ \
-I ${OCAMLDIR}lib/

CXXFLAGS := -O0 -g3 -Wall -fmessage-length=0 -fPIC

ifeq ($(OS),Darwin)
OCAMLLIB := /usr/local/lib/ocaml/
CXXFLAGS += -arch ${OCAMLARCH} -I ${OCAMLLIB}
else
ifeq ($(OS),LINUX)
OCAMLLIB := /usr/lib/ocaml/
CXXFLAGS += -I ${OCAMLLIB}
endif
endif

OCAMLSRCS := ${OCAMLDIR}config/configFile.ml ${OCAMLDIR}options.ml ${OCAMLDIR}log/logManager.ml ${OCAMLDIR}utils/utils.ml ${OCAMLDIR}symbolic/symbolic.ml ${OCAMLDIR}searchMethods/objectives/baseObjValue.ml ${OCAMLDIR}solution/solution.ml ${OCAMLDIR}lib/mainLib.ml ${OCAMLDIR}lib/symtrace.ml ${OCAMLDIR}lib/solutionManager.ml

OCAMLOBJS := ${OCAMLSRCS:%.ml=%.cmx}

CPPSRCS := ${CPPDIR}traces/BranchDistanceTrace.cpp ${CPPDIR}traces/SymbolicTrace.cpp ${CPPDIR}traces/Trace.cpp ${CPPDIR}sut.cpp ${CPPDIR}TraceManager.cpp

CPPHEADER := ${CPPSRCS:%.cpp=%.h}

CPPOBJS := ${CPPSRCS:%.cpp=%.o}

ifdef THIN
LIBOBJS := ${CPPOBJS} obj/camlcode.o
else
LIBOBJS := ${CPPOBJS} obj/camlcode.o extlib/libasmrun/*.o extlib/libperfcount/*.o extlib/libstr/*.o extlib/libunix/*.o
endif

%.cmx : %.ml
	${OCC} -o $@ ${OCAMLINCL} -c $<

obj/camlcode.o : ${OCAMLOBJS}
	${OCC} -output-obj -o obj/camlcode.o ${OCAMLINCL} str.cmxa unix.cmxa cil.cmxa ${OCAMLOBJS}
		
%.o : %.cpp
	${CC} -o $@ -c ${CXXFLAGS} $<

extlib/libasmrun/*.o : 
	cd extlib/libasmrun/; \
	ar -x ${OCAMLLIB}libasmrun.a
	 
asmrun : extlib/libasmrun/*.o

extlib/libunix/%.o : 
	cd extlib/libunix/; \
	ar -x ${OCAMLLIB}libunix.a
	
unix : extlib/libunix/%.o

extlib/libstr/%.o : 
	cd extlib/libstr/; \
	ar -x ${OCAMLLIB}libstr.a
	
str : extlib/libstr/%.o

extlib/libperfcount/%.o : 
	cd extlib/libperfcount/; \
	ar -x ${CILOBJ}libperfcount.a
	
perfcount : extlib/libperfcount/%.o

${LIBNAME} : ${LIBOBJS}
	ar -r "${LIBNAME}" ${LIBOBJS}
	
all : ${LIBNAME}
	
clean:
	-rm -f ${LIBNAME} 
	-rm -f ${CPPDIR}*.o
	-rm -f ${CPPDIR}traces/*.o
	-rm -f obj/camlcode.o
	-rm -f ${OCAMLOBJS} ${OCAMLSRCS:%.ml=%.cmi} ${OCAMLSRCS:%.ml=%.o} 
#	-rm -f ${ALIBDIR}extlib/libasmrun/*.o 
#	-rm -f ${ALIBDIR}extlib/libperfcount/*.o 
#	-rm -f ${ALIBDIR}extlib/libstr/*.o 
#	-rm -f ${ALIBDIR}extlib/libunix/*.o
