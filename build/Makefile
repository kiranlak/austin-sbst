ifdef THIN
export THIN
endif

all : 
	cd ../AustinLib ; ${MAKE} -f ../AustinLib/Makefile all
	cd ../AustinOcaml ; ${MAKE} -f ../AustinOcaml/Makefile all
	 
clean :
	cd ../AustinLib ;${MAKE} -f ../AustinLib/Makefile clean
	cd ../AustinOcaml ; ${MAKE} -f ../AustinOcaml/Makefile clean
	
	
# example sut.exe compilation
# g++ -o sut.exe /path to /austin_instrumented.o -L /path to austin lib/ -lAustinLib -ldl -lm
