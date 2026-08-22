#include "MAL.h"

#include "Environment.h"
#include "Reader.h"
#include "ReadLine.h"
#include "Types.h"

#include <iostream>

malValuePtr READ(const String& input);
String PRINT(malValuePtr ast);
String rep(const String& input, malEnvPtr env);

static malBuiltIn::ApplyFunc
    builtIn_add, builtIn_sub, builtIn_mul, builtIn_div;

int main(int argc, char* argv[])
{
    String prompt = "user> ";
    String input;
    malEnvPtr replEnv(new malEnv);
    replEnv->set("+", mal::builtin("+", &builtIn_add));
    replEnv->set("-", mal::builtin("-", &builtIn_sub));
    replEnv->set("*", mal::builtin("+", &builtIn_mul));
    replEnv->set("/", mal::builtin("/", &builtIn_div));
    while (s_readLine_get(prompt, input)) {
        std::cout << rep(input, replEnv) << "\n";
    }
    return 0;
}

String rep(const String& input, malEnvPtr env)
{
    try {
        return PRINT(EVAL(READ(input), env));
    }
    catch (malValuePtr& mv) {
        std::cerr << "Error: " << PRINT(mv) << "\n";
        return "";
    }
}

malValuePtr READ(const String& input)
{
    return readStr(input);
}

malValuePtr EVAL(malValuePtr ast, malEnvPtr env)
{
    // std::cout << "EVAL: " << PRINT(ast) << "\n";

        const malList* list = DYNAMIC_CAST(malList, ast);
        if (!list || (list->count() == 0)) {
            return ast->eval(env);
        }

        // From here on down we are evaluating a non-empty list.

        // Now we're left with the case of a regular list to be evaluated.
        auto op = VALUE_CAST(malApplicable, EVAL(list->item(0), env));
        malValueVec items;
        for (auto i = list->begin() + 1, e = list->end(); i != e; ++i) {
            items.push_back(EVAL(*i, env));
        }
        return op->apply(items.begin(), items.end());
}

String PRINT(malValuePtr ast)
{
    return ast->print(true);
}

#define ARG(type, name) type* name = VALUE_CAST(type, *argsBegin++)

#define CHECK_ARGS_IS(expected) \
    checkArgsIs(name.c_str(), expected, std::distance(argsBegin, argsEnd))

#define CHECK_ARGS_BETWEEN(min, max) \
    checkArgsBetween(name.c_str(), min, max, std::distance(argsBegin, argsEnd))


static malValuePtr builtIn_add(const String& name,
    malValueIter argsBegin, malValueIter argsEnd)
{
        CHECK_ARGS_IS(2);
        ARG(malInteger, lhs);
        ARG(malInteger, rhs);
        return mal::integer(lhs->value() + rhs->value());
}

static malValuePtr builtIn_sub(const String& name,
    malValueIter argsBegin, malValueIter argsEnd)
{
        int argCount = CHECK_ARGS_BETWEEN(1, 2);
        ARG(malInteger, lhs);
        if (argCount == 1) {
            return mal::integer(- lhs->value());
        }
        ARG(malInteger, rhs);
        return mal::integer(lhs->value() - rhs->value());
}

static malValuePtr builtIn_mul(const String& name,
    malValueIter argsBegin, malValueIter argsEnd)
{
        CHECK_ARGS_IS(2);
        ARG(malInteger, lhs);
        ARG(malInteger, rhs);
        return mal::integer(lhs->value() * rhs->value());
}

static malValuePtr builtIn_div(const String& name,
    malValueIter argsBegin, malValueIter argsEnd)
{
        CHECK_ARGS_IS(2);
        ARG(malInteger, lhs);
        ARG(malInteger, rhs);
        MAL_CHECK(rhs->value() != 0, "Division by zero"); \
        return mal::integer(lhs->value() / rhs->value());
}
