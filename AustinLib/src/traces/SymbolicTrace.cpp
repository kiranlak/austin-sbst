/*
 * SymbolicTrace.cpp
 *
 *  Created on: 19 Jul 2010
 *      Author: kiran
 */

#include "SymbolicTrace.h"

using namespace std;
using namespace austin;

LvalBase::LvalBase(void* address, unsigned int offset,
		void* targetAddr, lvalIdent ident) {
	this->address = address;
	this->offset = offset;
	this->targetAddress = targetAddress;
	this->id = ident;
}
LvalBase::LvalBase(const LvalBase& seed)
{
	this->address = seed.address;
	this->offset = seed.offset;
	this->targetAddress = seed.targetAddress;
	this->id = seed.id;
}
LvalBase::~LvalBase() {}

void* LvalBase::GetAddress() {
	return this->address;
}
unsigned int LvalBase::GetOffset() {
	return this->offset;
}
void* LvalBase::GetTargetAddress()
{
	return this->targetAddress;
}
template<typename T>
LvalValue<T>::LvalValue(void* address, unsigned int offset,
		void* targetAddr, T value) : LvalBase(address, offset, targetAddr, vptr)
{
	this->value = value;
}
template<typename T>
LvalValue<T>::LvalValue(const LvalValue<T>& seed) : LvalBase(seed)
{
	this->value = seed.value;
}
template<typename T>
LvalValue<T>* LvalValue<T>::Clone()
{
	LvalValue<T>* clone = new LvalValue<T>(*this);
	return clone;
}
template<typename T>
LvalValue<T>::~LvalValue()
{
}
template<typename T>
T LvalValue<T>::GetValue()
{
	return this->value;
}
template<typename T>
const char* LvalValue<T>::GetTypeName() {
	return typeid(T).name();
}
TraceItem::TraceItem(unsigned int sid, unsigned int index,
		bool branchingNode, LvalBase* lval, vector<LvalBase*>& rhs)
{
	this->sid = sid;
	this->index = index;
	this->branchingStmt = branchingNode;
	this->lval = lval;
	this->expressions = rhs;
}
TraceItem::TraceItem(const TraceItem& seed)
{
	this->sid = seed.sid;
	this->index = seed.index;
	this->branchingStmt = seed.branchingStmt;
	this->lval = seed.lval->Clone();
	vector<LvalBase*>::const_iterator it;
	for(it = seed.expressions.begin(); it != seed.expressions.end(); ++it)
	{
		this->expressions.push_back((*it)->Clone());
	}
}
TraceItem::~TraceItem()
{
	if(this->lval != NULL)
	{
		delete this->lval;
		this->lval = NULL;
	}
	vector<LvalBase*>::iterator it;
	for(it = this->expressions.begin(); it != this->expressions.end(); ++it)
	{
		delete *it;
	}
	this->expressions.clear();
}
SymbolicTrace::SymbolicTrace(const string& fname) : Trace(fname){
	// TODO Auto-generated constructor stub
}

SymbolicTrace::~SymbolicTrace() {
	// TODO Auto-generated destructor stub
	this->Trace::CloseTraceFile();
	vector<TraceItem*>::iterator it;
	for (it = this->trace.begin(); it != this->trace.end(); ++it)
	{
		delete *it;
	}
	this->trace.clear();
}
void SymbolicTrace::AddStatement(TraceItem* n) {
	this->trace.push_back(n);
}
void SymbolicTrace::Initialize(const string& outDir)
{
}

extern sig_atomic_t __AUSTIN__IGNORETIMEOUT;
SymbolicTrace* symtrace;
extern SolutionManager* solManager;

namespace austin{
void GetCILValuesFromLvalBase(LvalBase* item, char targetAddress[50], long double* fvalue, long long* ivalue)
{
	int cnt = 0;
	if(strcmp(item->GetTypeName(), typeid(void*).name()) == 0)
	{
		LvalValue<void*>* n = dynamic_cast<LvalValue<void*>* >(item);
		assert(n != NULL);
		if(n->GetValue() != NULL)
		{
			cnt = sprintf(targetAddress, "%p", n->GetValue());
			assert(cnt > 0);
		}
	}
	else if(strcmp(item->GetTypeName(), typeid(long long).name()) == 0)
	{
		LvalValue<long long>* n = dynamic_cast<LvalValue<long long>* >(item);
		assert(n != NULL);
		*ivalue = n->GetValue();
	}
	else if(strcmp(item->GetTypeName(), typeid(long double).name()) == 0)
	{
		LvalValue<long double>* n = dynamic_cast<LvalValue<long double>* >(item);
		assert(n != NULL);
		*fvalue = n->GetValue();
	}
	else
		throw runtime_error("invalid type in GetCILValuesFromLvalBase");
}
LvalBase* GetLvalAndExpressionVector(unsigned int len, va_list args, vector<LvalBase*>& traceItems)
{
	void* address = NULL;
	unsigned int offset = 0;
	void* targetAddr = NULL;
	char* format = NULL;
	LvalBase* lhs = NULL;
	LvalBase* item = NULL;
	for(unsigned int i = 0; i < len; ++i)
	{
		address = va_arg(args, void*);
		offset = va_arg(args, unsigned int);
		targetAddr = va_arg(args, void*);
		format = va_arg(args, char*);
		if(strcmp(format, "d") == 0)
		{
			item = new LvalValue<long long>(address, offset, targetAddr, va_arg(args, long long));
		}
		else if(strcmp(format, "f") == 0)
		{
			item = new LvalValue<long double>(address, offset, targetAddr, va_arg(args, long double));
		}
		else if(strcmp(format, "p") == 0)
		{
			item = new LvalValue<void*>(address, offset, targetAddr, va_arg(args, void*));
		}
		else
			throw runtime_error("unrecognized format string in Austin__SymLogStmt");

		if(lhs == NULL)
			lhs = item;
		else
		{
			traceItems.push_back(item);
		}
	}

	return lhs;
}
extern "C" CAMLprim value findAddressInformation(value tracePos, value vindex)
{
	CAMLparam2(tracePos, vindex);
	CAMLlocal1(resTuple);

	int iindex = Int_val(vindex);
	int ipos = Int_val(tracePos);

	char address[50];
	char targetAddress[50];
	unsigned int offset = 0;
	long double fvalue = 0;
	long long ivalue = 0;

	sprintf(address, "0x0");
	sprintf(targetAddress, "0x0");

	int cnt = 0;

	TraceItem* item = dynamic_cast<TraceItem*>(symtrace->trace[ipos]);
	assert(item != NULL);

	resTuple = caml_alloc(5, 0);

	if(iindex == -1)
	{
		//get lval addresses!!
		LvalBase* lvItem = item->lval;
		assert(lvItem != NULL);
		if(lvItem->GetAddress() != NULL)
		{
			cnt = sprintf(address, "%p", lvItem->GetAddress());
			assert(cnt > 0);
		}
		offset = lvItem->GetOffset();
		GetCILValuesFromLvalBase(lvItem, targetAddress, &fvalue, &ivalue);
	}
	else
	{
		assert(item->branchingStmt);
		assert(iindex >= 0);
		assert((unsigned int)iindex < item->expressions.size());

		LvalBase* expItem = item->expressions.at(iindex);

		if(expItem->GetAddress() != NULL)
		{
			cnt = sprintf(address, "%p", expItem->GetAddress());
			offset = expItem->GetOffset();
			assert(cnt > 0);
		}
		GetCILValuesFromLvalBase(expItem, targetAddress, &fvalue, &ivalue);
	}
	Store_field( resTuple, 0, caml_copy_string(address));
	Store_field( resTuple, 1, Val_int((int)offset));
	Store_field( resTuple, 2, caml_copy_string(targetAddress));
	Store_field( resTuple, 3, caml_copy_double((double)fvalue));
	Store_field( resTuple, 4, copy_int64(ivalue));
	CAMLreturn(resTuple);
}
extern "C" void Austin__SymexTrace()
{
	CAMLparam0();
	CAMLlocal3( cli, cons, tuple );

	__AUSTIN__IGNORETIMEOUT = 1;

	static value * closure_f = NULL;
	if (closure_f == NULL) {
		closure_f = caml_named_value("executeSymTrace");
		assert(closure_f != NULL);
	}

	int sid, index;

	cli = Val_emptylist;

	for (symtrace->cit = symtrace->trace.begin();
			symtrace->cit != symtrace->trace.end(); symtrace->cit++)
	{
		//call ocaml symex with sid, expect callback to ask for value....
		sid = (*(symtrace->cit))->sid;

		if((*symtrace->cit)->branchingStmt)
		{
			index = (dynamic_cast<TraceItem*>(*(symtrace->cit)))->index;
		}
		else
			index = -1;

		tuple = caml_alloc(2, 0);

		Store_field(tuple, 0, Val_int(sid));
		Store_field(tuple, 1, Val_int(index));

		cons = caml_alloc(2, 0);

		Store_field( cons, 0, tuple );  // head
		Store_field( cons, 1, cli );              // tail

		cli = cons;

		//caml_callback2(*closure_f, Val_int(sid), Val_int(index));
	}

	caml_callback(*closure_f, cli);

	CAMLreturn0;
}
}
extern "C" void Austin__SymLogStmt(unsigned int sid, unsigned int len, ...)
{
	/* format is void*, unsigned int, void*, char*, T (long long, long double, void*) */
	va_list args;

	va_start(args, len);

	LvalBase* lhs = NULL;
	vector<LvalBase*> expressions;

	lhs = GetLvalAndExpressionVector(len, args, expressions);

	TraceItem* traceItem = new TraceItem(sid, 0, false, lhs, expressions);

	symtrace->AddStatement(traceItem);

	va_end(args);
}
extern "C" void Austin__SymLogCall(unsigned int sid, unsigned int len, ...)
{
	/* format is void*, unsigned int, void*, char*, T (long long, long double, void*) */
	va_list args;

	va_start(args, len);

	LvalBase* lhs = NULL;
	vector<LvalBase*> expressions;

	lhs = GetLvalAndExpressionVector(len, args, expressions);

	TraceItem* traceItem = new TraceItem(sid, 0, false, lhs, expressions);

	symtrace->AddStatement(traceItem);

	va_end(args);
}
extern "C" void Austin__SymLogReturn(unsigned int sid, unsigned int len, ...)
{
	/* format is void*, unsigned int, void*, char*, T (long long, long double, void*) */
	va_list args;

	va_start(args, len);

	LvalBase* lhs = NULL;
	vector<LvalBase*> expressions;

	lhs = GetLvalAndExpressionVector(len, args, expressions);

	TraceItem* traceItem = new TraceItem(sid, 0, false, lhs, expressions);

	symtrace->AddStatement(traceItem);

	va_end(args);
}
extern "C" void Austin__SymUpdateReturn(unsigned int sid, unsigned int len, ...)
{
	/* format is void*, unsigned int, void*, char*, T (long long, long double, void*) */
	va_list args;

	va_start(args, len);

	LvalBase* lhs = NULL;
	vector<LvalBase*> expressions;

	lhs = GetLvalAndExpressionVector(len, args, expressions);

	TraceItem* traceItem = new TraceItem(sid, 0, false, lhs, expressions);

	symtrace->AddStatement(traceItem);

	va_end(args);
}
extern "C" void Austin__SymLogBranch(unsigned int sid, unsigned int index, unsigned int len, ...)
{
	/* format is void*, unsigned int, void*, char*, T (long long, long double, void*) */
	va_list args;

	va_start(args, len);

	LvalBase* lhs = NULL;
	vector<LvalBase*> expressions;

	lhs = GetLvalAndExpressionVector(len, args, expressions);

	/* I don't want lhs, so put lhs into tracItems */
	expressions.insert(expressions.begin(), lhs);

	lhs = NULL;

	TraceItem* traceItem = new TraceItem(sid, index, true, lhs, expressions);

	symtrace->AddStatement(traceItem);

	va_end(args);
}
