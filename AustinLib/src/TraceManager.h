/*
 * TraceManager.h
 *
 *  Created on: 19 Jul 2010
 *      Author: kiran
 */

#ifndef TRACEMANAGER_H_
#define TRACEMANAGER_H_

#include "traces/BranchDistanceTrace.h"
#include "traces/SymbolicTrace.h"

#include <iostream>
#include <fstream>
#include <stdexcept>

namespace austin {

enum traces{branch, symbolic};

inline traces operator++( traces &rs, int ) {
   return rs = (traces)(rs + 1);
}

class TraceManager {
public:
	TraceManager(const std::string&);
	virtual ~TraceManager();

	void CreateTrace(traces);
	void CreateAllTraces();
	Trace* GetTrace(traces);

private:
	std::string bdtraceName;
	std::string symtraceName;
	const std::string outDir;
};

}

#endif /* TRACEMANAGER_H_ */
