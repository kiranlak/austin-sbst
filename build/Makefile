ifdef THIN
export THIN
endif

OS := $(shell uname)
ARCH := $(shell arch)

all : 
	cd ../AustinLib ; ${MAKE} -f ../AustinLib/Makefile all
	cd ../AustinOcaml ; ${MAKE} -f ../AustinOcaml/Makefile all
	 
clean :
	cd ../AustinLib ;${MAKE} -f ../AustinLib/Makefile clean
	cd ../AustinOcaml ; ${MAKE} -f ../AustinOcaml/Makefile clean
	

release : 
	cd ../AustinLib ; ${MAKE} -f ../AustinLib/Makefile all
	cd ../AustinOcaml ; ${MAKE} -f ../AustinOcaml/Makefile all
	-rm -rf austin
	-rm -f austin-$(OS)-$(ARCH).tar
	mkdir austin
	mkdir austin/AustinLib
	cp -r ../AustinLib/extra austin/AustinLib/
	cp ../AustinLib/libAustinLib.a austin/AustinLib/
	mkdir austin/bin
	cp ../AustinOcaml/austin austin/bin/
	cp ../AustinOcaml/testRunner austin/bin/
	mkdir austin/docs
	cp ../docs/* austin/docs/
	tar -cf austin-$(OS)-$(ARCH).tar austin	
# example sut.exe compilation
# g++ -o sut.exe /path to /austin_instrumented.o -L /path to austin lib/ -lAustinLib -ldl -lm
