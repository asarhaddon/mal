#include "Debug.h"
#include "Environment.h"
#include "Validation.h"

// make CPPFLAGS=-DDEBUG_ENV_LIFETIMES
#if DEBUG_ENV_LIFETIMES
static size_t allocs = 0;
#endif

malEnv::malEnv(malEnvPtr outer)
: m_outer(outer)
{
#if DEBUG_ENV_LIFETIMES
    TRACE("Create  env  %lu %p outer=%p\n", ++allocs, this, m_outer.ptr());
#endif
}

malEnv::malEnv(malEnvPtr outer, const StringVec& bindings,
               malValueIter argsBegin, malValueIter argsEnd)
: malEnv(outer)
{
    int n = bindings.size();
    auto it = argsBegin;
    for (int i = 0; i < n; i++) {
        if (bindings[i] == "&") {
            MAL_CHECK(i == n - 2, "There must be one parameter after the &");

            set(bindings[n-1], mal::list(it, argsEnd));
            return;
        }
        MAL_CHECK(it != argsEnd, "Not enough parameters");
        set(bindings[i], *it);
        ++it;
    }
    MAL_CHECK(it == argsEnd, "Too many parameters");
}

malEnv::~malEnv()
{
#if DEBUG_ENV_LIFETIMES
    TRACE("Destroy env  %lu %p outer=%p\n", --allocs, this, m_outer.ptr());
#endif
}

malValuePtr malEnv::get(const String& symbol) const
{
    for (auto env = this; env; env = env->m_outer.ptr()) {
        auto it = env->m_map.find(symbol);
        if (it != env->m_map.end()) {
            return it->second;
        }
    }
    return NULL;
}

malValuePtr malEnv::set(const String& symbol, malValuePtr value)
{
    m_map[symbol] = value;
    return value;
}
