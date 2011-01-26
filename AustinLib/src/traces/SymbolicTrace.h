/*
 * SymbolicTrace.h
 *
 *  Created on: 19 Jul 2010
 *      Author: kiran
 */

#ifndef SYMBOLICTRACE_H_
#define SYMBOLICTRACE_H_

#define BITSIZE(T) sizeof(T)*CHAR_BIT

#include "Trace.h"
#include "../sut.h"

#include <stdarg.h>
#include <limits.h>

#include <typeinfo>
#include <vector>
#include <stdexcept>
#include <cstring>

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

#ifdef __cplusplus
}
#endif


namespace austin {

#ifdef __cplusplus
extern "C" {
#endif

CAMLprim value findAddressInformation(value, value);

void Austin__SymLogStmt(unsigned int, unsigned int, ...);
void Austin__SymLogCall(unsigned int, unsigned int, ...) ;
void Austin__SymLogReturn(unsigned int, unsigned int, ...);
void Austin__SymUpdateReturn(unsigned int, unsigned int, ...);
void Austin__SymLogBranch(unsigned int, unsigned int, unsigned int, ...);
void Austin__SymexTrace();

#ifdef __cplusplus
}
#endif

enum lvalIdent{ll,ld,vptr};

class LvalBase
{
public:
	LvalBase(void*,unsigned int, void*, lvalIdent);
	LvalBase(const LvalBase&);
	virtual ~LvalBase();
	virtual const char* GetTypeName() = 0;
	virtual LvalBase* Clone() = 0;

	void* GetAddress();
	unsigned int GetOffset();
	void* GetTargetAddress();

	lvalIdent id;

private:
	void* address;
	unsigned int offset;
	void* targetAddress;
};

template<class T>
class LvalValue : public LvalBase
{
public:
	LvalValue(void*,unsigned int,void*, T);
	LvalValue(const LvalValue&);
	virtual ~LvalValue();

	const char* GetTypeName();
	LvalValue* Clone();

	T GetValue();
private:
	T value;
};

class TraceItem
{
public:
	TraceItem(unsigned int, unsigned int, bool, LvalBase*, std::vector<LvalBase*>&);
	TraceItem(const TraceItem&);
	virtual ~ TraceItem();

	unsigned int sid;
	unsigned int index;
	bool branchingStmt;
	LvalBase* lval;
	std::vector<LvalBase*> expressions;
};
class SymbolicTrace : public Trace {
public:
	SymbolicTrace(const std::string&);
	virtual ~SymbolicTrace();
	void AddStatement(TraceItem*);

	void Initialize(const std::string&);

	friend CAMLprim value findAddressInformation(value, value);
	friend void Austin__SymexTrace();

private:
	std::vector<TraceItem*> trace;
	std::vector<TraceItem*>::const_iterator cit;
};

void GetCILValuesFromLvalBase(LvalBase*, char[50], long double*, long long*);

}

#endif /* SYMBOLICTRACE_H_ */
