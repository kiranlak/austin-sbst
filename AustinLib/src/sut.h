/*
 * sut.h
 *
 *  Created on: 10 Apr 2010
 *      Author: kiran
 */

#ifndef SUT_H_
#define SUT_H_

#include "TraceManager.h"

#include <signal.h>
#include <stdlib.h>

#include <csignal>
#include <map>
#include <vector>
#include <iostream>

#ifdef __cplusplus
extern "C" {
#endif

#include <curses.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/misc.h>
#include <caml/alloc.h>
#include <caml/custom.h>
#include <caml/callback.h>
#include <caml/fail.h>

void Austin__Debug(char*);
void Austin__Setup(int, char**);
void Austin__Teardown();
void Austin__Assert(int);
void Austin__Raise(int);

void Austin__AddPrecon(const char*, const char*);

void Austin__ClearWorkItems();

void Austin__Free(void*);
void* Austin__Realloc(void*, size_t);

double Austin__GetPODNode(void*, int, int);

char Austin__GetCharValue(void*, unsigned int, unsigned int);
signed char Austin__GetSCharValue(void*, unsigned int, unsigned int);
unsigned char Austin__GetUCharValue(void*, unsigned int, unsigned int);
bool Austin__GetBoolValue(void*, unsigned int, unsigned int);
int Austin__GetIntValue(void*, unsigned int, unsigned int);
unsigned int Austin__GetUIntValue(void*, unsigned int, unsigned int);
short Austin__GetShortValue(void*, unsigned int, unsigned int);
unsigned short Austin__GetUShortValue(void*, unsigned int, unsigned int);
long Austin__GetLongValue(void*, unsigned int, unsigned int);
unsigned long Austin__GetULongValue(void*, unsigned int, unsigned int);
long long Austin__GetLongLongValue(void*, unsigned int, unsigned int);
unsigned long long Austin__GetULongLongValue(void*, unsigned int, unsigned int);

float Austin__GetFloatValue(void*, unsigned int, unsigned int);
double Austin__GetDoubleValue(void*, unsigned int, unsigned int);
long double Austin__GetLongDoubleValue(void*, unsigned int, unsigned int);

void* Austin__GetPtr(unsigned int, int*, void*, void (*)(void*,void*));
void* Austin__GetArray(unsigned int, void*);

#ifdef __cplusplus
}
#endif

namespace austin {

void InitializeOcamlRuntime();

class MemoryManager
{
public:
	MemoryManager();
	~MemoryManager();

	void* AddMalloc(size_t);
	void AddMalloc(void*);

	void RemoveMalloc(void*);
	void FreeMalloc(void*);
	void FreeMallocs();
private:
	std::vector<void*> mallocs;
};

typedef struct WorkItem
{
	unsigned int sourceId;
	unsigned int targetId;
	bool takesAddressOf;
	void* sourceAddress;
	void (*assignmentFunction)(void*, void*);
	WorkItem& operator=(WorkItem& rhs)
	{
		if(this != &rhs)
		{
			sourceId = rhs.sourceId;
			targetId = rhs.targetId;
			takesAddressOf = rhs.takesAddressOf;
			sourceAddress = rhs.sourceAddress;
			assignmentFunction = rhs.assignmentFunction;
		}
		return *this;
	}
}WorkItem;

class SolutionManager
{
public:
	SolutionManager(const std::string&);
	~SolutionManager();

	void AddWorkItem(unsigned int, unsigned int, void*, bool, void (*)(void*,void*));
	void ClearWorklist();

	void* GetPointerAddress(int);
	void* GetPointerMem(int);
	void SetPointerMemory(int, void*, void*);

	MemoryManager memManager;
	struct PointerInfo
	{
		int id;
		void* address;
		void* targetLoc;
		PointerInfo(int id, void* addr, void* target)
		{
			this->id = id;
			this->address = addr;
			this->targetLoc = target;
		}
	};
private:
	std::map<int, PointerInfo> pointerLocs;
	std::vector<WorkItem> delayedInputInitializations;

	unsigned int GetNextKey();
};

const int sutTimeout = 30;
const std::string keyAustinLibDir("austinLibDir");
const std::string keyAustinOutDir("austinOutDir");
}

#endif /* SUT_H_ */
