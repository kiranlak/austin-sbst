ALIBDIR := ../AustinLib/
ALIBSRCDIR := ${ALIBDIR}src/
ACAMLDIR := ../AustinOcaml/

LIBOUTNAME := ../libAustinLib.a

OCC := ocamlopt
CC := g++

OCCFLAGS := -I ${CILOBJ} -I ${ACAMLDIR} -I ${ACAMLDIR}config/ -I ${ACAMLDIR}log/ -I ${ACAMLDIR}utils/ -I ${ACAMLDIR}symbolic/ -I ${ACAMLDIR}searchMethods/objectives/ -I ${ACAMLDIR}solution/ -I ${ACAMLDIR}lib/

CCFLAGS := -O0 -g3 -Wall -fmessage-length=0 -fPIC

ifeq ($(OS),Darwin)
OCCLIBS := /usr/local/lib/ocaml/
CCFLAGS += -arch ${OCCARCH} -I ${OCCLIBS}
else
ifeq ($(OS),LINUX)
OCCLIBS := /usr/lib/ocaml/
CCFLAGS += -I ${OCCLIBS}
endif
endif

OCAMLSOURCES := ${ACAMLDIR}config/configFile.ml ${ACAMLDIR}options.ml ${ACAMLDIR}log/logManager.ml ${ACAMLDIR}utils/utils.ml ${ACAMLDIR}symbolic/symbolic.ml ${ACAMLDIR}searchMethods/objectives/baseObjValue.ml ${ACAMLDIR}solution/solution.ml ${ACAMLDIR}lib/mainLib.ml ${ACAMLDIR}lib/symtrace.ml ${ACAMLDIR}lib/solutionManager.ml

OCAMLOBJECTS := ${OCAMLSOURCES:%.ml=%.cmx}

CPPSOURCES := ${ALIBSRCDIR}traces/BranchDistanceTrace.cpp ${ALIBSRCDIR}traces/SymbolicTrace.cpp ${ALIBSRCDIR}traces/Trace.cpp ${ALIBSRCDIR}sut.cpp ${ALIBSRCDIR}TraceManager.cpp

CPPHEADER := ${CPPSOURCES:%.cpp=%.h}

CPPOBJS := ${CPPSOURCES:%.cpp=%.o}

ifdef THIN
LIBOBJS := ${CPPOBJS} ${ALIBDIR}obj/camlcode.o
else
LIBOBJS := ${CPPOBJS} ${ALIBDIR}obj/camlcode.o ${ALIBDIR}extlib/libasmrun/*.o ${ALIBDIR}extlib/libperfcount/*.o ${ALIBDIR}extlib/libstr/*.o ${ALIBDIR}extlib/libunix/*.o
endif

%.cmx : %.ml
	${OCC} -o $@ ${OCCFLAGS} -c $<

${ALIBDIR}obj/camlcode.o : ${OCAMLOBJECTS}
	ocamlopt -output-obj -o ${ALIBDIR}obj/camlcode.o ${OCCFLAGS} str.cmxa unix.cmxa cil.cmxa ${OCAMLOBJECTS}
		
%.o : %.cpp
	${CC} -o $@ -c ${CCFLAGS} $<

${ALIBDIR}extlib/libasmrun/*.o : 
	cd ${ALIBDIR}extlib/libasmrun/; \
	ar -x ${OCCLIBS}libasmrun.a
	 
asmrun : ${ALIBDIR}extlib/libasmrun/*.o

${ALIBDIR}extlib/libunix/%.o : 
	cd ${ALIBDIR}extlib/libunix/; \
	ar -x ${OCCLIBS}libunix.a
	
unix : ${ALIBDIR}extlib/libunix/%.o

${ALIBDIR}extlib/libstr/%.o : 
	cd ${ALIBDIR}extlib/libstr/; \
	ar -x ${OCCLIBS}libstr.a
	
str : ${ALIBDIR}extlib/libstr/%.o

${ALIBDIR}extlib/libperfcount/%.o : 
	cd ${ALIBDIR}extlib/libperfcount/; \
	ar -x ${CILOBJ}libperfcount.a
	
perfcount : ${ALIBDIR}extlib/libperfcount/%.o

${LIBOUTNAME} : ${LIBOBJS}
	ar -r "${LIBOUTNAME}" ${LIBOBJS}
	
alib : ${LIBOUTNAME}
	
clean:
	-rm -f ${LIBOUTNAME} 
	-rm -f ${ALIBSRCDIR}*.o
	-rm -f ${ALIBSRCDIR}traces/*.o
	-rm -f ${ACAMLDIR}*.cmi ${ACAMLDIR}*.o ${ACAMLDIR}*.cmx
	-rm -f ${ACAMLDIR}config/*.cmi ${ACAMLDIR}config/*.o ${ACAMLDIR}config/*.cmx
	-rm -f ${ACAMLDIR}log/*.cmi ${ACAMLDIR}log/*.o ${ACAMLDIR}log/*.cmx
	-rm -f ${ACAMLDIR}lib/*.cmi ${ACAMLDIR}lib/*.o ${ACAMLDIR}lib/*.cmx
	-rm -f ${ACAMLDIR}searchMethods/objectives/*.cmi ${ACAMLDIR}searchMethods/objectives/*.o ${ACAMLDIR}searchMethods/objectives/*.cmx
	-rm -f ${ACAMLDIR}solution/*.cmi ${ACAMLDIR}solution/*.o ${ACAMLDIR}solution/*.cmx
	-rm -f ${ACAMLDIR}symbolic/*.cmi ${ACAMLDIR}symbolic/*.o ${ACAMLDIR}symbolic/*.cmx
	-rm -f ${ACAMLDIR}utils/*.cmi ${ACAMLDIR}utils/*.o ${ACAMLDIR}utils/*.cmx
	-rm -f ${ALIBDIR}obj/camlcode.o 
#	-rm -f ${ALIBDIR}extlib/libasmrun/*.o 
#	-rm -f ${ALIBDIR}extlib/libperfcount/*.o 
#	-rm -f ${ALIBDIR}extlib/libstr/*.o 
#	-rm -f ${ALIBDIR}extlib/libunix/*.o
