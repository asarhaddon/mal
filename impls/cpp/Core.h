#pragma once

#include "Environment.h"
#include "Types.h"

void installCore();

extern const malEnvPtr replEnv;                  // step*.cpp
extern malValuePtr EVAL(malValuePtr, malEnvPtr); // step*.cpp
