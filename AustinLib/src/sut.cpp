/*
 * sut.cpp
 *
 *  Created on: 10 Apr 2010
 *      Author: kiran
 */
#include "sut.h"

using namespace std;
using namespace austin;

MemoryManager::MemoryManager(){}
MemoryManager::~MemoryManager()
{
	FreeMallocs();
}
void* MemoryManager::AddMalloc(size_t bytes)
{
	void* mem = malloc(bytes);
	AddMalloc(mem);
	return mem;
}
void MemoryManager::AddMalloc(void* mem)
{
	unsigned int size = this->mallocs.size();
	for(unsigned int i = 0; i < size; i++)
	{
		if(this->mallocs.at(i) == mem)
		{
			return;
		}
	}
	this->mallocs.push_back(mem);
}
void MemoryManager::RemoveMalloc(void* mem)
{
	vector<void*>::iterator it;
	for(it = this->mallocs.begin() ; it < this->mallocs.end(); ++it)
	{
		if(*it == mem)
		{
			this->mallocs.erase(it);
			free(mem);
			return;
		}
	}
}
void MemoryManager::FreeMalloc(void* mem)
{
	if(mem != NULL)
	{
		RemoveMalloc(mem);
	}
}
void MemoryManager::FreeMallocs()
{
	vector<void*>::iterator it;
	for(it = this->mallocs.begin() ; it != this->mallocs.end(); ++it)
	{
		if(*it != NULL)
		{
			free(*it);
			*it = NULL;
		}
	}
	this->mallocs.clear();
}

SolutionManager::SolutionManager(const string& outDir)
{

}
SolutionManager::~SolutionManager()
{
	this->delayedInputInitializations.clear();
	this->pointerLocs.clear();
}
void* SolutionManager::GetPointerAddress(int tid)
{
	map<int, PointerInfo>::const_iterator it;
	it = this->pointerLocs.find(tid);
	if(it == this->pointerLocs.end())
		return NULL;
	else
	{
		return it->second.address;
	}
}
void* SolutionManager::GetPointerMem(int tid)
{
	map<int, PointerInfo>::const_iterator it;
	it = this->pointerLocs.find(tid);
	if(it == this->pointerLocs.end())
		return NULL;
	else
	{
		return it->second.targetLoc;
	}
}
void SolutionManager::SetPointerMemory(int id, void* address, void* target)
{
	PointerInfo info(id, address, target);
	map<int, PointerInfo>::iterator it;
	it = this->pointerLocs.find(id);
	if(it == this->pointerLocs.end())
		this->pointerLocs.insert(pair<int, PointerInfo>(id, info));
	else
	{
		it->second.id = id;
		it->second.address = address;
		it->second.targetLoc = target;
	}
}
void SolutionManager::AddWorkItem(unsigned int sourceId, unsigned int targetId,
		void* sourceAddress, bool takesAddressOf,
		void (*assignmentFunc)(void* source, void* target))
{
	WorkItem item;
	item.sourceId = sourceId;
	item.targetId = targetId;
	item.sourceAddress = sourceAddress;
	item.takesAddressOf = takesAddressOf;
	item.assignmentFunction = assignmentFunc;
	this->delayedInputInitializations.push_back(item);
}
void SolutionManager::ClearWorklist()
{
	unsigned int size = this->delayedInputInitializations.size();
	for(unsigned int i = 0; i < size; i++)
	{
		WorkItem item = this->delayedInputInitializations.at(i);
		map<int, PointerInfo>::const_iterator it;
		it = this->pointerLocs.find(item.targetId);
		if(it == this->pointerLocs.end())
			continue;
		else
		{
			if(item.takesAddressOf)
			{
				item.assignmentFunction(item.sourceAddress, it->second.address);
			}
			else
			{
				item.assignmentFunction(item.sourceAddress, it->second.targetLoc);
			}
		}
	}
	this->delayedInputInitializations.clear();
}
/* GLOBALS */
SolutionManager* solManager = NULL;
TraceManager* traceManager = NULL;

void InitializeOcamlRuntime(string& outDir, string& libDir)
{
	CAMLparam0();
	CAMLlocal2(cmlOut, cmlLib);

	char * argv[] = { NULL };

	caml_startup(argv);

	static value * closure_f = NULL;
	if (closure_f == NULL) {
		closure_f = caml_named_value("initializeOcaml");
		assert(closure_f != NULL);
	}

	cmlOut = caml_copy_string(outDir.c_str());
	cmlLib = caml_copy_string(libDir.c_str());

	caml_callback2(*closure_f, cmlOut, cmlLib);

	CAMLreturn0;
}
extern "C" void Austin__Debug(char* msg)
{
	cout << "AustinLib Debug:" << msg << endl;
}
extern "C" void Austin__Setup(int argc, char** argv)
{
	string outDir;
	string libDir;
	for(int i = 0; i < argc; ++i)
	{
		if(strcmp(argv[i], keyAustinLibDir.c_str()) == 0)
		{
			libDir = argv[i + 1];
			++i;
		}
		else if(strcmp(argv[i], keyAustinOutDir.c_str()) == 0)
		{
			outDir = argv[i + 1];
			++i;
		}
	}
	solManager = new SolutionManager(outDir);
	traceManager = new TraceManager(outDir);
	traceManager->CreateAllTraces();
	InitializeOcamlRuntime(outDir, libDir);
	/**TODO: add alarm timeout when executing sut */
	//alarm(5);
}
extern "C" void Austin__Teardown()
{
	CAMLparam0();

	static value * closure_f = NULL;

	if(solManager != NULL)
	{
		delete solManager;
		solManager = NULL;
	}
	if(traceManager != NULL)
	{
		delete traceManager;
		traceManager = NULL;
	}

	if (closure_f == NULL) {
		closure_f = caml_named_value("closeLogChannel");
		assert(closure_f != NULL);
	}

	caml_callback(*closure_f, Val_unit);

	CAMLreturn0;
}
extern "C" void Austin__Assert(int outcome)
{
	if(!outcome)
	{
		raise(SIGABRT);
	}
}
extern "C" void Austin__Raise(int sig)
{
	raise(sig);
}
extern "C" void Austin__Assume(unsigned int argc, ...)
{
	va_list ap;

	va_start(ap, argc);

	bool error = false;

	for (unsigned int i = 0; i < argc; i++)
	{
		if(!va_arg(ap, int))
		{
			error = true;
			break;
		}
	}

	va_end(ap);

	if(error)
	{
		exit(255);
	}
}
extern "C" void Austin__Assume__Init(unsigned int argc, ...)
{
	static bool initialCheck = true;

	if(initialCheck)
	{
		va_list ap;

		va_start(ap, argc);

		bool error = false;

		for (unsigned int i = 0; i < argc; i++)
		{
			if(!va_arg(ap, int))
			{
				error = true;
				break;
			}
		}

		va_end(ap);

		if(error)
		{
			exit(254);
		}
	}

	initialCheck = false;
}
extern "C" void Austin__Assume__Array(unsigned int len, ...)
{

}
extern "C" void Austin__ClearWorkItems()
{
	assert(solManager != NULL);
	solManager->ClearWorklist();
}
extern "C" void Austin__Free(void* mem)
{
	assert(solManager != NULL);
	solManager->memManager.FreeMalloc(mem);
}
extern "C" void* Austin__Malloc(size_t size)
{
	assert(solManager != NULL);
	return solManager->memManager.AddMalloc(size);
}
extern "C" void* Austin__Realloc(void* mem, size_t size)
{
	assert(solManager != NULL);
	solManager->memManager.RemoveMalloc(mem);
	return realloc(mem, size);
}
extern "C" double Austin__GetPODNode(void* address, int offset, int width)
{
	CAMLparam0();
	CAMLlocal1(fval);

	double dval = 0;
	char buffer[50];
	int n;
	static value* closure_f = NULL;

	if (closure_f == NULL) {
		closure_f = caml_named_value("getNextPODNode");
		assert(closure_f != NULL);
	}

	n = sprintf(buffer, "%p", address);

	assert(n > 0);

	fval = caml_callback3(*closure_f, caml_copy_string(buffer), Val_int(offset), Val_int(width));

	dval = Double_val(fval);

	CAMLreturnT(double, dval);
}
extern "C" char Austin__GetCharValue(void* address, unsigned int offset, unsigned int width)
{
	return (char)Austin__GetPODNode(address, (int)offset, (int)width);
}
extern "C" signed char Austin__GetSCharValue(void* address, unsigned int offset, unsigned int width)
{
	return (signed char)Austin__GetPODNode(address, (int)offset, (int)width);
}
extern "C" unsigned char Austin__GetUCharValue(void* address, unsigned int offset, unsigned int width)
{
	return (unsigned char)Austin__GetPODNode(address, (int)offset, (int)width);
}
extern "C" bool Austin__GetBoolValue(void* address, unsigned int offset, unsigned int width)
{
	return (bool)Austin__GetPODNode(address, (int)offset, (int)width);
}
extern "C" int Austin__GetIntValue(void* address, unsigned int offset, unsigned int width)
{
	return (int)Austin__GetPODNode(address, (int)offset, (int)width);
}
extern "C" unsigned int Austin__GetUIntValue(void* address, unsigned int offset, unsigned int width)
{
	return (unsigned int)Austin__GetPODNode(address, (int)offset, (int)width);
}
extern "C" short Austin__GetShortValue(void* address, unsigned int offset, unsigned int width)
{
	return (short)Austin__GetPODNode(address, (int)offset, (int)width);
}
extern "C" unsigned short Austin__GetUShortValue(void* address, unsigned int offset, unsigned int width)
{
	return (unsigned short)Austin__GetPODNode(address, (int)offset, (int)width);
}
extern "C" long Austin__GetLongValue(void* address, unsigned int offset, unsigned int width)
{
	return (long)Austin__GetPODNode(address, (int)offset, (int)width);
}
extern "C" unsigned long Austin__GetULongValue(void* address, unsigned int offset, unsigned int width)
{
	return (unsigned long)Austin__GetPODNode(address, (int)offset, (int)width);
}
extern "C" long long Austin__GetLongLongValue(void* address, unsigned int offset, unsigned int width)
{
	return (long long)Austin__GetPODNode(address, (int)offset, (int)width);
}
extern "C" unsigned long long Austin__GetULongLongValue(void* address, unsigned int offset, unsigned int width)
{
	return (unsigned long long)Austin__GetPODNode(address, (int)offset, (int)width);
}

extern "C" float Austin__GetFloatValue(void* address, unsigned int offset, unsigned int width)
{
	return (float)Austin__GetPODNode(address, (int)offset, (int)width);
}
extern "C" double Austin__GetDoubleValue(void* address, unsigned int offset, unsigned int width)
{
	return Austin__GetPODNode(address, (int)offset, (int)width);
}
extern "C" long double Austin__GetLongDoubleValue(void* address, unsigned int offset, unsigned int width)
{
	return (long double)Austin__GetPODNode(address, (int)offset, (int)width);
}

extern "C" void* Austin__GetPtr(unsigned int size, int* proceed, void* address,
		void (*assignmentFunction)(void* s,void* t))
{
	CAMLparam0();
	CAMLlocal1(tuple);

	assert(solManager != NULL);

	void* mem = NULL;
	char buffer[50];
	int n;
	static value * closure_f = NULL;

	if (closure_f == NULL) {
		closure_f = caml_named_value("getNextPointerNode");
		assert(closure_f != NULL);
	}

	n = sprintf(buffer, "%p", address);

	assert(n > 0);

	tuple = caml_callback(*closure_f, caml_copy_string(buffer));

	int id = Int_val(Field(tuple, 0));

	int tid = Int_val(Field(tuple, 1));
	int isNull = Bool_val(Field(tuple, 2));
	int isAddrOf = Bool_val(Field(tuple, 3));

	if(isNull == 1)
	{
		*proceed = 0;
	}
	else if(tid == -1)
	{
		*proceed = 1;
		mem = solManager->memManager.AddMalloc(size);
	}
	else
	{
		*proceed = 0;

		if(isAddrOf == 1)
		{
			if(id < tid)
			{
				solManager->AddWorkItem(id, tid, address, true, assignmentFunction);
			}
			else
			{
				mem = solManager->GetPointerAddress(tid);
			}
		}
		else
		{
			if(id < tid)
			{
				solManager->AddWorkItem(id, tid, address, false, assignmentFunction);
			}
			else
			{
				mem = solManager->GetPointerMem(tid);
			}
		}
	}

	solManager->SetPointerMemory(id, address, mem);

	CAMLreturnT(void*, mem);
}
extern "C" void* Austin__GetArray(unsigned int size, void* address)
{
	assert(solManager != NULL);
	return solManager->memManager.AddMalloc(size);
}
