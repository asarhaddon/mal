#include "Environment.h"
#include "Reader.h"
#include "ReadLine.h"
#include "Types.h"
#include "Validation.h"

#include <iostream>

malValuePtr READ(const String& input);
String PRINT(malValuePtr ast);
String rep(const String& input, malEnvPtr env);
malValuePtr EVAL(malValuePtr ast, malEnvPtr env);

static malEnvPtr replEnv(new malEnv);

static malBuiltIn::ApplyFunc
    builtIn_add, builtIn_sub, builtIn_mul, builtIn_div;

int main(int, char*[])
{
    String prompt = "user> ";
    String input;
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
       auto dbgenv = env->get("DEBUG-EVAL");
       if (dbgenv && dbgenv->isTrue()) {
           std::cout << "EVAL: " << PRINT(ast) << "\n";
       }

        if (auto symbol = DYNAMIC_CAST(malSymbol, ast)) {
            auto key = symbol->value();
            auto value = env->get(key);
            MAL_CHECK(value, "'%s' not found", key.c_str());
            return value;
        }
        if (auto map = DYNAMIC_CAST(malHash, ast)) {
            return map->fmap([env] (malValuePtr x) { return EVAL(x, env); });
        }
        if (auto vector = DYNAMIC_CAST(malVector, ast)) {
            return vector->fmap([env] (malValuePtr x) { return EVAL(x, env); });
        }
        const malList* list = DYNAMIC_CAST(malList, ast);
        if (!list || (list->count() == 0)) {
            return ast;
        }

        // From here on down we are evaluating a non-empty list.
        // First handle the special forms.
        if (const malSymbol* symbol = DYNAMIC_CAST(malSymbol, list->item(0))) {
            String special = symbol->value();
            int argCount = list->count() - 1;

            if (special == "def!") {
                checkArgsIs("def!", 2, argCount);
                const malSymbol* id = VALUE_CAST("def!", malSymbol, list->item(1));
                return env->set(id->value(), EVAL(list->item(2), env));
            }

            if (special == "let*") {
                checkArgsIs("let*", 2, argCount);
                const malSequence* bindings =
                    VALUE_CAST("let*", malSequence, list->item(1));
                int count = checkArgsEven("let*", bindings->count());
                malEnvPtr inner(new malEnv(env));
                for (int i = 0; i < count; i += 2) {
                    const malSymbol* var =
                        VALUE_CAST("let*", malSymbol, bindings->item(i));
                    inner->set(var->value(), EVAL(bindings->item(i+1), inner));
                }
                return EVAL(list->item(2), inner);
            }
        }

        // Now we're left with the case of a regular list to be evaluated.
        auto op = VALUE_CAST("EVAL apply phase", malApplicable,
                             EVAL(list->item(0), env));
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

#define ARG(type, var) type* var = VALUE_CAST(name, type, *argsBegin++)

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
