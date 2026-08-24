#pragma once

#include <stdio.h>
#include <stdlib.h>

#define DEBUG_TRACE_FILE    stderr

#define TRACE(...) fprintf(DEBUG_TRACE_FILE, __VA_ARGS__)

#define _ASSERT(file, line, condition, ...) \
    if (!(condition)) { \
        printf("Assertion failed at %s(%d): ", file, line); \
        printf(__VA_ARGS__); \
        exit(1); \
    } else { }


#define ASSERT(condition, ...) \
    _ASSERT(__FILE__, __LINE__, condition, __VA_ARGS__)
