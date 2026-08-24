#pragma once

#include "String.h"
#include "Types.h"

#include <gc/gc_allocator.h>
#include <gc/gc_cpp.h>

#include <unordered_map>

class malEnv : public gc {
public:
    malEnv(malEnvPtr outer = NULL);
    malEnv(malEnvPtr outer,
           const StringVec& bindings,
           malValueIter argsBegin,
           malValueIter argsEnd);

    malValuePtr get(const String& symbol) const;
    // NULL means not found

    malValuePtr set(const String& symbol, malValuePtr value);

private:
    typedef std::unordered_map<String, malValuePtr,
                               std::hash<String>, std::equal_to<String>,
                               gc_allocator<std::pair<const String,
                                                      malValuePtr>>>
        Map;
    Map m_map;
    const malEnvPtr m_outer;
};
