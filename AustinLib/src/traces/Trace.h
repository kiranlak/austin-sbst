/*
 * Trace.h
 *
 *  Created on: 19 Jul 2010
 *      Author: kiran
 */

#ifndef TRACE_H_
#define TRACE_H_

#include <assert.h>
#include <string>
#include <iostream>
#include <fstream>
#include <sstream>

namespace austin {

class Trace {
public:
	Trace(const std::string&);
	virtual ~Trace();

	virtual void Initialize(const std::string&){}

	void OpenTraceFile();
	void CloseTraceFile();

protected:
	std::ofstream ofs;
	const std::string fileName;
};

}

#endif /* TRACE_H_ */
