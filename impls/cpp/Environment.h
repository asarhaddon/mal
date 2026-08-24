#pragma once

#include "RefCountedPtr.h"
#include "String.h"
#include "Types.h"

#include <unordered_map>

class malEnv : public RefCounted {
public:
    malEnv(malEnvPtr outer = NULL);
    malEnv(malEnvPtr outer,
           const StringVec& bindings,
           malValueIter argsBegin,
           malValueIter argsEnd);

    ~malEnv();

    malValuePtr get(const String& symbol) const;
    // NULL means not found

    malValuePtr set(const String& symbol, malValuePtr value);

private:
    typedef std::unordered_map<String, malValuePtr> Map;
    Map m_map;
    const malEnvPtr m_outer;
};
