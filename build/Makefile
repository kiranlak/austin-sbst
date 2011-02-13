OS := $(shell uname)

ifeq ($(OS),Linux)
OS := LINUX
endif

OCCARCH=$(subst architecture:,,$(shell ocamlopt -config | grep architecture: ))

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

export OS
export OCCARCH
export CILOBJ

thin-lib :
	${MAKE} -f lib/makefile alib THIN=yes

fat-lib :
	${MAKE} -f lib/makefile alib

byte :
	${MAKE} -f austin/makefile bin BYTE=yes

native :
	${MAKE} -f austin/makefile bin

all : 
	${MAKE} native
	${MAKE} fat-lib
	 
clean :
	${MAKE} -f lib/makefile clean
	${MAKE} -f austin/makefile clean
