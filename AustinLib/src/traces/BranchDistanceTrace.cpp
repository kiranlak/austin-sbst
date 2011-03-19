/*
 * BranchDistanceTrace.cpp
 *
 *  Created on: 19 Jul 2010
 *      Author: kiran
 */

#include "BranchDistanceTrace.h"

using namespace std;
using namespace austin;

BranchDistanceTrace::BranchDistanceTrace(const string& fname)
	: Trace(fname), key ("__TRACE__bd__"), sep (",")
{
	// TODO Auto-generated constructor stub
}

BranchDistanceTrace::~BranchDistanceTrace() {
	// TODO Auto-generated destructor stub
	this->Trace::CloseTraceFile();
}

BranchDistanceTrace* bdtrace;

extern "C" long double Austin__Min(long double d1, long double d2)
{
	if(d1 <= d2) return d1;
	else return d2;
}
extern "C" long double Austin__Max(long double d1, long double d2)
{
	if(d1 >= d2) return d1;
	else return d2;
}
namespace austin {
extern "C" void Austin__SendBranchDistances(unsigned int fid, unsigned int nid,
		unsigned int index, unsigned int values, ...)
{
	assert(values > 0);
	va_list ap;

	va_start(ap, values);

	assert(bdtrace != NULL);

	bdtrace->Trace::OpenTraceFile();

	bdtrace->ofs << fid << bdtrace->sep << nid << bdtrace->sep << index << bdtrace->sep;

	for (unsigned int i = 0; i < values; i++)
	{
		/**TODO: Make setprecision configurable parameter */
		bdtrace->ofs << fixed << setprecision(16) << va_arg(ap, long double) << bdtrace->sep;
	}

	bdtrace->ofs << endl;

	bdtrace->Trace::CloseTraceFile();

	va_end(ap);
}
}
long double validateF(float res)
{
	if(res != res)
		return 1;
	else
		return res;
}
long double validateF(double res)
{
	if(res != res)
		return 1;
	else
		return res;
}
long double validateF(long double res)
{
	if(res != res)
		return 1;
	else
		return res;
}
extern "C" {
long double Austin__EvalEquals__Void(void* lhs, void* rhs)
{
	if(lhs == rhs) return 0;
	else return 1;
}
long double Austin__EvalEquals__Char(char lhs, char rhs)
{
	if(lhs == rhs) return 0;
	else return abs((int)(lhs - rhs));
}
long double Austin__EvalEquals__SChar(signed char lhs, signed char rhs)
{
	if(lhs == rhs) return 0;
	else return abs((int)(lhs - rhs));
}
long double Austin__EvalEquals__UChar(unsigned char lhs, unsigned char rhs)
{
	if(lhs == rhs) return 0;
	else return abs((int)(lhs - rhs));
}
long double Austin__EvalEquals__Bool(bool lhs, bool rhs)
{
	return (lhs == rhs)? 1:0;
}
long double Austin__EvalEquals__Int(int lhs, int rhs)
{
	if(lhs == rhs) return 0;
	else return abs(lhs - rhs);
}
long double Austin__EvalEquals__UInt(unsigned int lhs, unsigned int rhs)
{
	if(lhs == rhs) return 0;
	else
	{
		double res = fabs((double)(lhs - rhs));
		return validateF(res);
	}
}
long double Austin__EvalEquals__Short(short lhs, short rhs)
{
	if(lhs == rhs) return 0;
	else return abs((int)(lhs - rhs));
}
long double Austin__EvalEquals__UShort(unsigned short lhs, unsigned short rhs)
{
	if(lhs == rhs) return 0;
	else return abs((int)(lhs - rhs));
}
long double Austin__EvalEquals__Long(long lhs, long rhs)
{
	if(lhs == rhs) return 0;
	else return labs(lhs - rhs);
}
long double Austin__EvalEquals__ULong(unsigned long lhs, unsigned long rhs)
{
	if(lhs == rhs) return 0;
	else
	{
		double res = fabs((double)(lhs - rhs));
		return validateF(res);
	}
}
long double Austin__EvalEquals__LongLong(long long lhs, long long rhs)
{
	if(lhs == rhs) return 0;
	else
	{
		long double res = fabs((long double)(lhs - rhs));
		return validateF(res);
	}
}
long double Austin__EvalEquals__ULongLong(unsigned long long lhs, unsigned long long rhs)
{
	if(lhs == rhs) return 0;
	else
	{
		long double res = fabs((long double)(lhs - rhs));
		return validateF(res);
	}
}
long double Austin__EvalEquals__Float(float lhs, float rhs)
{
	if(lhs == rhs) return 0;
	else
	{
		float res = fabs(lhs - rhs);
		return validateF(res);
	}
}
long double Austin__EvalEquals__Double(double lhs, double rhs)
{
	if(lhs == rhs) return 0;
	else
	{
		double res = fabs(lhs - rhs);
		return validateF(res);
	}
}
long double Austin__EvalEquals__LongDouble(long double lhs, long double rhs)
{
	if(lhs == rhs) return 0;
	else
	{
		long double res = fabs(lhs - rhs);
		return validateF(res);
	}
}

long double Austin__EvalNotEqual__Void(void* lhs, void* rhs)
{
	if(lhs != rhs) return 0;
	else return FAILURE_CONSTANT;
}
long double Austin__EvalNotEqual__Char(char lhs, char rhs)
{
	if(lhs != rhs) return 0;
	else
	{
		return FAILURE_CONSTANT;
	}
}
long double Austin__EvalNotEqual__SChar(signed char lhs, signed char rhs)
{
	if(lhs != rhs) return 0;
	else
	{
		return FAILURE_CONSTANT;
	}
}
long double Austin__EvalNotEqual__UChar(unsigned char lhs, unsigned char rhs)
{
	if(lhs != rhs) return 0;
	else
	{
		return FAILURE_CONSTANT;
	}
}
long double Austin__EvalNotEqual__Bool(bool lhs, bool rhs)
{
	return (lhs != rhs)? 0:1;
}
long double Austin__EvalNotEqual__Int(int lhs, int rhs)
{
	if(lhs != rhs) return 0;
	else
	{
		return FAILURE_CONSTANT;
	}
}
long double Austin__EvalNotEqual__UInt(unsigned int lhs, unsigned int rhs)
{
	if(lhs != rhs) return 0;
	else
	{
		return FAILURE_CONSTANT;
	}
}
long double Austin__EvalNotEqual__Short(short lhs, short rhs)
{
	if(lhs != rhs) return 0;
	else
	{
		return FAILURE_CONSTANT;
	}
}
long double Austin__EvalNotEqual__UShort(unsigned short lhs, unsigned short rhs)
{
	if(lhs != rhs) return 0;
	else
	{
		return FAILURE_CONSTANT;
	}
}
long double Austin__EvalNotEqual__Long(long lhs, long rhs)
{
	if(lhs != rhs) return 0;
	else
	{
		return FAILURE_CONSTANT;
	}
}
long double Austin__EvalNotEqual__ULong(unsigned long lhs, unsigned long rhs)
{
	if(lhs != rhs) return 0;
	else
	{
		return FAILURE_CONSTANT;
	}
}
long double Austin__EvalNotEqual__LongLong(long long lhs, long long rhs)
{
	if(lhs != rhs) return 0;
	else
	{
		return FAILURE_CONSTANT;
	}
}
long double Austin__EvalNotEqual__ULongLong(unsigned long long lhs, unsigned long long rhs)
{
	if(lhs != rhs) return 0;
	else
	{
		return FAILURE_CONSTANT;
	}
}
long double Austin__EvalNotEqual__Float(float lhs, float rhs)
{
	if(lhs != rhs) return 0;
	else
	{
		return FAILURE_CONSTANT;
	}
}
long double Austin__EvalNotEqual__Double(double lhs, double rhs)
{
	if(lhs != rhs) return 0;
	else
	{
		return FAILURE_CONSTANT;
	}
}
long double Austin__EvalNotEqual__LongDouble(long double lhs, long double rhs)
{
	if(lhs != rhs) return 0;
	else
	{
		return FAILURE_CONSTANT;
	}
}

long double Austin__EvalLessThan__Void(void* lhs, void* rhs)
{
	if(lhs < rhs) return 0;
	else return 1;
}
long double Austin__EvalLessThan__Char(char lhs, char rhs)
{
	if(lhs < rhs)
		return 0;
	else
		return (long double)((char)((char)(lhs - rhs) + 1));
}
long double Austin__EvalLessThan__SChar(signed char lhs, signed char rhs)
{
	if(lhs < rhs)
		return 0;
	else
		return (long double)((signed char)((signed char)(lhs - rhs) + 1));
}
long double Austin__EvalLessThan__UChar(unsigned char lhs, unsigned char rhs)
{
	if(lhs < rhs)
		return 0;
	else
		return (long double)((signed char)((unsigned char)(lhs - rhs) + 1));
}
long double Austin__EvalLessThan__Bool(bool lhs, bool rhs)
{
	if(lhs == false && rhs == true)
		return 0;
	else
		return 1;
}
long double Austin__EvalLessThan__Int(int lhs, int rhs)
{
	if(lhs < rhs)
		return 0;
	else
		return (long double)((int)((int)(lhs - rhs) + 1));
}
long double Austin__EvalLessThan__UInt(unsigned int lhs, unsigned int rhs)
{
	if(lhs < rhs)
		return 0;
	else
		return (long double)((unsigned int)((unsigned int)(lhs - rhs) + 1));
}
long double Austin__EvalLessThan__Short(short lhs, short rhs)
{
	if(lhs < rhs)
		return 0;
	else
		return (long double)((short)((short)(lhs - rhs) + 1));
}
long double Austin__EvalLessThan__UShort(unsigned short lhs, unsigned short rhs)
{
	if(lhs < rhs)
		return 0;
	else
		return (long double)((unsigned int)((unsigned short)(lhs - rhs) + 1));
}
long double Austin__EvalLessThan__Long(long lhs, long rhs)
{
	if(lhs < rhs)
		return 0;
	else
		return (long double)((long)((long)(lhs - rhs) + 1));
}
long double Austin__EvalLessThan__ULong(unsigned long lhs, unsigned long rhs)
{
	if(lhs < rhs)
		return 0;
	else
		return (long double)((unsigned long)((unsigned long)(lhs - rhs) + 1));
}
long double Austin__EvalLessThan__LongLong(long long lhs, long long rhs)
{
	if(lhs < rhs)
		return 0;
	else
		return (long double)((long long)((long long)(lhs - rhs) + 1));
}
long double Austin__EvalLessThan__ULongLong(unsigned long long lhs, unsigned long long rhs)
{
	if(lhs < rhs)
		return 0;
	else
		return (long double)((unsigned long long)((unsigned long long)(lhs - rhs) + 1));
}
long double Austin__EvalLessThan__Float(float lhs, float rhs)
{
	if(lhs < rhs)
		return 0;
	else
	{
		float res = lhs - rhs;
		res = validateF(res);
		return (res + 1);
	}
}
long double Austin__EvalLessThan__Double(double lhs, double rhs)
{
	if(lhs < rhs)
		return 0;
	else
	{
		double res = lhs - rhs;
		res = validateF(res);
		return (res + 1);
	}
}
long double Austin__EvalLessThan__LongDouble(long double lhs, long double rhs)
{
	if(lhs < rhs)
		return 0;
	else
	{
		long double res = lhs - rhs;
		res = validateF(res);
		return (res + 1);
	}
}

long double Austin__EvalGreaterThan__Void(void* lhs, void* rhs)
{
	if(lhs > rhs) return 0;
	else return 1;
}
long double Austin__EvalGreaterThan__Char(char lhs, char rhs)
{
	if(lhs > rhs)
		return 0;
	else
		return (long double)((char)((char)(rhs - lhs) + 1));
}
long double Austin__EvalGreaterThan__SChar(signed char lhs, signed char rhs)
{
	if(lhs > rhs)
		return 0;
	else
		return (long double)((signed char)((signed char)(rhs - lhs) + 1));
}
long double Austin__EvalGreaterThan__UChar(unsigned char lhs, unsigned char rhs)
{
	if(lhs > rhs)
		return 0;
	else
		return (long double)((unsigned char)((unsigned char)(rhs - lhs) + 1));
}
long double Austin__EvalGreaterThan__Bool(bool lhs, bool rhs)
{
	if(lhs == true && rhs == false)
		return 0;
	else
		return 1;
}
long double Austin__EvalGreaterThan__Int(int lhs, int rhs)
{
	if(lhs > rhs)
		return 0;
	else
		return (long double)((int)((int)(rhs - lhs) + 1));
}
long double Austin__EvalGreaterThan__UInt(unsigned int lhs, unsigned int rhs)
{
	if(lhs > rhs)
		return 0;
	else
		return (long double)((unsigned int)((unsigned int)(rhs - lhs) + 1));
}
long double Austin__EvalGreaterThan__Short(short lhs, short rhs)
{
	if(lhs > rhs)
		return 0;
	else
		return (long double)((short)((short)(rhs - lhs) + 1));
}
long double Austin__EvalGreaterThan__UShort(unsigned short lhs, unsigned short rhs)
{
	if(lhs > rhs)
		return 0;
	else
		return (long double)((unsigned short)((unsigned short)(rhs - lhs) + 1));
}
long double Austin__EvalGreaterThan__Long(long lhs, long rhs)
{
	if(lhs > rhs)
		return 0;
	else
		return (long double)((long)((long)(rhs - lhs) + 1));
}
long double Austin__EvalGreaterThan__ULong(unsigned long lhs, unsigned long rhs)
{
	if(lhs > rhs)
		return 0;
	else
		return (long double)((unsigned long)((unsigned long)(rhs - lhs) + 1));
}
long double Austin__EvalGreaterThan__LongLong(long long lhs, long long rhs)
{
	if(lhs > rhs)
		return 0;
	else
		return (long double)((long long)((long long)(rhs - lhs) + 1));
}
long double Austin__EvalGreaterThan__ULongLong(unsigned long long lhs, unsigned long long rhs)
{
	if(lhs > rhs)
		return 0;
	else
		return (long double)((unsigned long long)((unsigned long long)(rhs - lhs) + 1));
}
long double Austin__EvalGreaterThan__Float(float lhs, float rhs)
{
	if(lhs > rhs)
		return 0;
	else
	{
		float res = rhs - lhs;
		res = validateF(res);
		return (res + 1);
	}
}
long double Austin__EvalGreaterThan__Double(double lhs, double rhs)
{
	if(lhs > rhs)
		return 0;
	else
	{
		double res = rhs - lhs;
		res = validateF(res);
		return (res + 1);
	}
}
long double Austin__EvalGreaterThan__LongDouble(long double lhs, long double rhs)
{
	if(lhs > rhs)
		return 0;
	else
	{
		long double res = rhs - lhs;
		res = validateF(res);
		return (res + 1);
	}
}

long double Austin__EvalLessThanEq__Void(void* lhs, void* rhs)
{
	if(lhs <= rhs) return 0;
	else return 1;
}
long double Austin__EvalLessThanEq__Char(char lhs, char rhs)
{
	if(lhs <= rhs)
		return 0;
	else
		return (long double)((char)((char)(lhs - rhs) + 1));
}
long double Austin__EvalLessThanEq__SChar(signed char lhs, signed char rhs)
{
	if(lhs <= rhs)
		return 0;
	else
		return (long double)((signed char)((signed char)(lhs - rhs) + 1));
}
long double Austin__EvalLessThanEq__UChar(unsigned char lhs, unsigned char rhs)
{
	if(lhs <= rhs)
		return 0;
	else
		return (long double)((unsigned char)((unsigned char)(lhs - rhs) + 1));
}
long double Austin__EvalLessThanEq__Bool(bool lhs, bool rhs)
{
	if(lhs == false && rhs == true)
		return 0;
	else
		return 1;
}
long double Austin__EvalLessThanEq__Int(int lhs, int rhs)
{
	if(lhs <= rhs)
		return 0;
	else
		return (long double)((int)((int)(lhs - rhs) + 1));
}
long double Austin__EvalLessThanEq__UInt(unsigned int lhs, unsigned int rhs)
{
	if(lhs <= rhs)
		return 0;
	else
		return (long double)((unsigned int)((unsigned int)(lhs - rhs) + 1));
}
long double Austin__EvalLessThanEq__Short(short lhs, short rhs)
{
	if(lhs <= rhs)
		return 0;
	else
		return (long double)((short)((short)(lhs - rhs) + 1));
}
long double Austin__EvalLessThanEq__UShort(unsigned short lhs, unsigned short rhs)
{
	if(lhs <= rhs)
		return 0;
	else
		return (long double)((unsigned short)((unsigned short)(lhs - rhs) + 1));
}
long double Austin__EvalLessThanEq__Long(long lhs, long rhs)
{
	if(lhs <= rhs)
		return 0;
	else
		return (long double)((long)((long)(lhs - rhs) + 1));
}
long double Austin__EvalLessThanEq__ULong(unsigned long lhs, unsigned long rhs)
{
	if(lhs <= rhs)
		return 0;
	else
		return (long double)((unsigned long)((unsigned long)(lhs - rhs) + 1));
}
long double Austin__EvalLessThanEq__LongLong(long long lhs, long long rhs)
{
	if(lhs <= rhs)
		return 0;
	else
		return (long double)((long long)((long long)(lhs - rhs) + 1));
}
long double Austin__EvalLessThanEq__ULongLong(unsigned long long lhs, unsigned long long rhs)
{
	if(lhs <= rhs)
		return 0;
	else
		return (long double)((unsigned long long)((unsigned long long)(lhs - rhs) + 1));
}
long double Austin__EvalLessThanEq__Float(float lhs, float rhs)
{
	if(lhs <= rhs)
		return 0;
	else
	{
		float res = lhs - rhs;
		res = validateF(res);
		return (res + 1);
	}
}
long double Austin__EvalLessThanEq__Double(double lhs, double rhs)
{
	if(lhs <= rhs)
		return 0;
	else
	{
		double res = lhs - rhs;
		res = validateF(res);
		return (res + 1);
	}
}
long double Austin__EvalLessThanEq__LongDouble(long double lhs, long double rhs)
{
	if(lhs <= rhs)
		return 0;
	else
	{
		long double res = lhs - rhs;
		res = validateF(res);
		return (res + 1);
	}
}

long double Austin__EvalGreaterThanEq__Void(void* lhs, void* rhs)
{
	if(lhs >= rhs) return 0;
	else return 1;
}
long double Austin__EvalGreaterThanEq__Char(char lhs, char rhs)
{
	if(lhs >= rhs)
		return 0;
	else
		return (long double)((char)((char)(rhs - lhs) + 1));
}
long double Austin__EvalGreaterThanEq__SChar(signed char lhs, signed char rhs)
{
	if(lhs >= rhs)
		return 0;
	else
		return (long double)((signed char)((signed char)(rhs - lhs) + 1));
}
long double Austin__EvalGreaterThanEq__UChar(unsigned char lhs, unsigned char rhs)
{
	if(lhs >= rhs)
		return 0;
	else
		return (long double)((unsigned char)((unsigned char)(rhs - lhs) + 1));
}
long double Austin__EvalGreaterThanEq__Bool(bool lhs, bool rhs)
{
	if(lhs == true && rhs == false)
		return 0;
	else
		return 1;
}
long double Austin__EvalGreaterThanEq__Int(int lhs, int rhs)
{
	if(lhs >= rhs)
		return 0;
	else
		return (long double)((int)((int)(rhs - lhs) + 1));
}
long double Austin__EvalGreaterThanEq__UInt(unsigned int lhs, unsigned int rhs)
{
	if(lhs >= rhs)
		return 0;
	else
		return (long double)((unsigned int)((unsigned int)(rhs - lhs) + 1));
}
long double Austin__EvalGreaterThanEq__Short(short lhs, short rhs)
{
	if(lhs >= rhs)
		return 0;
	else
		return (long double)((short)((short)(rhs - lhs) + 1));
}
long double Austin__EvalGreaterThanEq__UShort(unsigned short lhs, unsigned short rhs)
{
	if(lhs >= rhs)
		return 0;
	else
		return (long double)((unsigned short)((unsigned short)(rhs - lhs) + 1));
}
long double Austin__EvalGreaterThanEq__Long(long lhs, long rhs)
{
	if(lhs >= rhs)
		return 0;
	else
		return (long double)((long)((long)(rhs - lhs) + 1));
}
long double Austin__EvalGreaterThanEq__ULong(unsigned long lhs, unsigned long rhs)
{
	if(lhs >= rhs)
		return 0;
	else
		return (long double)((unsigned long)((unsigned long)(rhs - lhs) + 1));
}
long double Austin__EvalGreaterThanEq__LongLong(long long lhs, long long rhs)
{
	if(lhs >= rhs)
		return 0;
	else
		return (long double)((long long)((long long)(rhs - lhs) + 1));
}
long double Austin__EvalGreaterThanEq__ULongLong(unsigned long long lhs, unsigned long long rhs)
{
	if(lhs >= rhs)
		return 0;
	else
		return (long double)((unsigned long long)((unsigned long long)(rhs - lhs) + 1));
}
long double Austin__EvalGreaterThanEq__Float(float lhs, float rhs)
{
	if(lhs >= rhs)
		return 0;
	else
	{
		float res = rhs - lhs;
		res = validateF(res);
		return (res + 1);
	}
}
long double Austin__EvalGreaterThanEq__Double(double lhs, double rhs)
{
	if(lhs >= rhs)
		return 0;
	else
	{
		double res = rhs - lhs;
		res = validateF(res);
		return (res + 1);
	}
}
long double Austin__EvalGreaterThanEq__LongDouble(long double lhs, long double rhs)
{
	if(lhs >= rhs)
		return 0;
	else
	{
		long double res = rhs - lhs;
		res = validateF(res);
		return (res + 1);
	}
}

}
