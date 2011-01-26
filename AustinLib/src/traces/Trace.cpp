/*
 * Trace.cpp
 *
 *  Created on: 19 Jul 2010
 *      Author: kiran
 */

#include "Trace.h"

using namespace std;
using namespace austin;

Trace::Trace(const string& fname) : fileName(fname)
{
	//OpenTraceFile();
}
Trace::~Trace()
{
	CloseTraceFile();
}
void Trace::OpenTraceFile()
{
	if(this->ofs.is_open())
		this->ofs.close();
	this->ofs.open(this->fileName.c_str(), ios::out | ios::app);//ofs.open(fileName.c_str(), ios::out | ios::binary | ios::app);
}
void Trace::CloseTraceFile()
{
	if(this->ofs.is_open())
		this->ofs.close();
}
