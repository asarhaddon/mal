#pragma once

#include "String.h"

#define MAL_CHECK(condition, ...)  \
    if (condition) { } else throw mal::string(STRF(__VA_ARGS__));

#define MAL_FAIL(...) MAL_CHECK(false, __VA_ARGS__)

extern void checkArgsIs(const char* name, int expected, int got);
extern void checkArgsBetween(const char* name, int min, int max, int got);
extern void checkArgsAtLeast(const char* name, int min, int got);
extern void checkArgsEven(const char* name, int got);
