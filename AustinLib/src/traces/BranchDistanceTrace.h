/*
 * BranchDistanceTrace.h
 *
 *  Created on: 19 Jul 2010
 *      Author: kiran
 */

#ifndef BRANCHDISTANCETRACE_H_
#define BRANCHDISTANCETRACE_H_

#include "Trace.h"

#include <cmath>
#include <stdarg.h>
#include <cstdlib>
#include <iomanip>

namespace austin {

#ifdef __cplusplus
extern "C" {
#endif
void Austin__SendBranchDistances(unsigned int, unsigned int, unsigned int, unsigned int,...);
#ifdef __cplusplus
}
#endif

#define FAILURE_CONSTANT 1

class BranchDistanceTrace : public Trace {
public:
	BranchDistanceTrace(const std::string&);
	virtual ~BranchDistanceTrace();
	friend void Austin__SendBranchDistances(unsigned int, unsigned int, unsigned int, unsigned int,...);
private:
	const std::string key;
	const std::string sep;
};

}

#ifdef __cplusplus
extern "C" {
#endif
long double Austin__Min(long double, long double);
long double Austin__Max(long double, long double);

long double Austin__EvalEquals__Void(void*, void*);
long double Austin__EvalEquals__Char(char, char);
long double Austin__EvalEquals__SChar(signed char, signed char);
long double Austin__EvalEquals__UChar(unsigned char, unsigned char);
long double Austin__EvalEquals__Bool(bool, bool);
long double Austin__EvalEquals__Int(int, int);
long double Austin__EvalEquals__UInt(unsigned int, unsigned int);
long double Austin__EvalEquals__Short(short, short);
long double Austin__EvalEquals__UShort(unsigned short, unsigned short);
long double Austin__EvalEquals__Long(long, long);
long double Austin__EvalEquals__ULong(unsigned long, unsigned long);
long double Austin__EvalEquals__LongLong(long long, long long);
long double Austin__EvalEquals__ULongLong(unsigned long long, unsigned long long);
long double Austin__EvalEquals__Float(float, float);
long double Austin__EvalEquals__Double(double, double);
long double Austin__EvalEquals__LongDouble(long double, long double);

long double Austin__EvalNotEqual__Void(void*, void*);
long double Austin__EvalNotEqual__Char(char, char);
long double Austin__EvalNotEqual__SChar(signed char, signed char);
long double Austin__EvalNotEqual__UChar(unsigned char, unsigned char);
long double Austin__EvalNotEqual__Bool(bool, bool);
long double Austin__EvalNotEqual__Int(int, int);
long double Austin__EvalNotEqual__UInt(unsigned int, unsigned int);
long double Austin__EvalNotEqual__Short(short, short);
long double Austin__EvalNotEqual__UShort(unsigned short, unsigned short);
long double Austin__EvalNotEqual__Long(long, long);
long double Austin__EvalNotEqual__ULong(unsigned long, unsigned long);
long double Austin__EvalNotEqual__LongLong(long long, long long);
long double Austin__EvalNotEqual__ULongLong(unsigned long long, unsigned long long);
long double Austin__EvalNotEqual__Float(float, float);
long double Austin__EvalNotEqual__Double(double, double);
long double Austin__EvalNotEqual__LongDouble(long double, long double);

long double Austin__EvalLessThan__Void(void*, void*);
long double Austin__EvalLessThan__Char(char, char);
long double Austin__EvalLessThan__SChar(signed char, signed char);
long double Austin__EvalLessThan__UChar(unsigned char, unsigned char);
long double Austin__EvalLessThan__Bool(bool, bool);
long double Austin__EvalLessThan__Int(int, int);
long double Austin__EvalLessThan__UInt(unsigned int, unsigned int);
long double Austin__EvalLessThan__Short(short, short);
long double Austin__EvalLessThan__UShort(unsigned short, unsigned short);
long double Austin__EvalLessThan__Long(long, long);
long double Austin__EvalLessThan__ULong(unsigned long, unsigned long);
long double Austin__EvalLessThan__LongLong(long long, long long);
long double Austin__EvalLessThan__ULongLong(unsigned long long, unsigned long long);
long double Austin__EvalLessThan__Float(float, float);
long double Austin__EvalLessThan__Double(double, double);
long double Austin__EvalLessThan__LongDouble(long double, long double);

long double Austin__EvalGreaterThan__Void(void*, void*);
long double Austin__EvalGreaterThan__Char(char, char);
long double Austin__EvalGreaterThan__SChar(signed char, signed char);
long double Austin__EvalGreaterThan__UChar(unsigned char, unsigned char);
long double Austin__EvalGreaterThan__Bool(bool, bool);
long double Austin__EvalGreaterThan__Int(int, int);
long double Austin__EvalGreaterThan__UInt(unsigned int, unsigned int);
long double Austin__EvalGreaterThan__Short(short, short);
long double Austin__EvalGreaterThan__UShort(unsigned short, unsigned short);
long double Austin__EvalGreaterThan__Long(long, long);
long double Austin__EvalGreaterThan__ULong(unsigned long, unsigned long);
long double Austin__EvalGreaterThan__LongLong(long long, long long);
long double Austin__EvalGreaterThan__ULongLong(unsigned long long, unsigned long long);
long double Austin__EvalGreaterThan__Float(float, float);
long double Austin__EvalGreaterThan__Double(double, double);
long double Austin__EvalGreaterThan__LongDouble(long double, long double);

long double Austin__EvalLessThanEq__Void(void*, void*);
long double Austin__EvalLessThanEq__Char(char, char);
long double Austin__EvalLessThanEq__SChar(signed char, signed char);
long double Austin__EvalLessThanEq__UChar(unsigned char, unsigned char);
long double Austin__EvalLessThanEq__Bool(bool, bool);
long double Austin__EvalLessThanEq__Int(int, int);
long double Austin__EvalLessThanEq__UInt(unsigned int, unsigned int);
long double Austin__EvalLessThanEq__Short(short, short);
long double Austin__EvalLessThanEq__UShort(unsigned short, unsigned short);
long double Austin__EvalLessThanEq__Long(long, long);
long double Austin__EvalLessThanEq__ULong(unsigned long, unsigned long);
long double Austin__EvalLessThanEq__LongLong(long long, long long);
long double Austin__EvalLessThanEq__ULongLong(unsigned long long, unsigned long long);
long double Austin__EvalLessThanEq__Float(float, float);
long double Austin__EvalLessThanEq__Double(double, double);
long double Austin__EvalLessThanEq__LongDouble(long double, long double);

long double Austin__EvalGreaterThanEq__Void(void*, void*);
long double Austin__EvalGreaterThanEq__Char(char, char);
long double Austin__EvalGreaterThanEq__SChar(signed char, signed char);
long double Austin__EvalGreaterThanEq__UChar(unsigned char, unsigned char);
long double Austin__EvalGreaterThanEq__Bool(bool, bool);
long double Austin__EvalGreaterThanEq__Int(int, int);
long double Austin__EvalGreaterThanEq__UInt(unsigned int, unsigned int);
long double Austin__EvalGreaterThanEq__Short(short, short);
long double Austin__EvalGreaterThanEq__UShort(unsigned short, unsigned short);
long double Austin__EvalGreaterThanEq__Long(long, long);
long double Austin__EvalGreaterThanEq__ULong(unsigned long, unsigned long);
long double Austin__EvalGreaterThanEq__LongLong(long long, long long);
long double Austin__EvalGreaterThanEq__ULongLong(unsigned long long, unsigned long long);
long double Austin__EvalGreaterThanEq__Float(float, float);
long double Austin__EvalGreaterThanEq__Double(double, double);
long double Austin__EvalGreaterThanEq__LongDouble(long double, long double);


#ifdef __cplusplus
}
#endif

#endif /* BRANCHDISTANCETRACE_H_ */
