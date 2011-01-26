/*
 * TraceManager.cpp
 *
 *  Created on: 19 Jul 2010
 *      Author: kiran
 */

#include "TraceManager.h"

using namespace std;
using namespace austin;

extern BranchDistanceTrace* bdtrace;
extern SymbolicTrace* symtrace;

TraceManager::TraceManager(const string& outDir) : outDir(outDir)
{
	// TODO Auto-generated constructor stub
	bdtraceName = outDir;
	symtraceName = outDir;

	bdtraceName = bdtraceName.append("/traceInfo.dat");
	symtraceName = symtraceName.append("/symInfo.dat");

	bdtrace = NULL;
	symtrace = NULL;
}

TraceManager::~TraceManager() {
	// TODO Auto-generated destructor stub
	if(bdtrace!= NULL)
	{
		delete bdtrace;
		bdtrace = NULL;
	}
	if(symtrace != NULL)
	{
		delete symtrace;
		symtrace = NULL;
	}
}
void TraceManager::CreateTrace(traces t)
{
	switch(t)
	{
	case branch:
		if(bdtrace != NULL)
			delete bdtrace;
		bdtrace = new BranchDistanceTrace(this->bdtraceName);
		bdtrace->Initialize(this->outDir);
		break;
	case symbolic:
		if(symtrace != NULL)
			delete symtrace;
		symtrace = new SymbolicTrace(this->symtraceName);
		symtrace->Initialize(this->outDir);
		break;
	default: throw runtime_error("Unrecognzied trace");
	}
}
void TraceManager::CreateAllTraces()
{
	for(traces t = branch; t <= symbolic; t++)
	{
		CreateTrace(t);
	}
}
Trace* TraceManager::GetTrace(traces t)
{
	switch(t)
	{
	case branch:
		return bdtrace;
	case symbolic:
		return symtrace;
	default: throw runtime_error("Couldn't get trace (unrecognized)");
	}
}
