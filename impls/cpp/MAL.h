#ifndef INCLUDE_MAL_H
#define INCLUDE_MAL_H

#include "RefCountedPtr.h"
#include "String.h"
#include "Validation.h"

#include <vector>

class malValue;
typedef RefCountedPtr<malValue>  malValuePtr;
typedef std::vector<malValuePtr> malValueVec;
typedef malValueVec::iterator    malValueIter;

class malEnv;
typedef RefCountedPtr<malEnv>     malEnvPtr;

// step*.cpp
extern malValuePtr EVAL(malValuePtr ast, malEnvPtr env);

#endif // INCLUDE_MAL_H
