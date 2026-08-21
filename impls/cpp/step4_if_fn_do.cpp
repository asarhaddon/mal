#include "Core.h"
#include "Environment.h"
#include "Reader.h"
#include "ReadLine.h"
#include "Types.h"
#include "Validation.h"

#include <iostream>

malValuePtr READ(const String& input);
String PRINT(malValuePtr ast);
static void installFunctions(malEnvPtr env);
String rep(const String& input, malEnvPtr env);
malValuePtr EVAL(malValuePtr ast, malEnvPtr env);

const malEnvPtr replEnv(new malEnv);

int main(int argc, char* argv[])
{
    String prompt = "user> ";
    String input;
    installCore();
    installFunctions(replEnv);
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

            if (special == "do") {
                checkArgsAtLeast("do", 1, argCount);

                for (int i = 1; i < argCount; i++) {
                    EVAL(list->item(i), env);
                }
                return EVAL(list->item(argCount), env);
            }

            if (special == "fn*") {
                checkArgsIs("fn*", 2, argCount);

                const malSequence* bindings =
                    VALUE_CAST("fn*", malSequence, list->item(1));
                StringVec params;
                for (int i = 0; i < bindings->count(); i++) {
                    const malSymbol* sym =
                        VALUE_CAST("fn*", malSymbol, bindings->item(i));
                    params.push_back(sym->value());
                }

                malValuePtr body = list->item(2);
                malLambda::ApplyFunc apply =
                    [body, env, params] (malValueIter b, malValueIter e)
                    { return EVAL(body, new malEnv(env, params, b, e)); };
                return mal::lambda(apply, params, body, env);
            }

            if (special == "if") {
                checkArgsBetween("if", 2, 3, argCount);

                bool isTrue = EVAL(list->item(1), env)->isTrue();
                if (!isTrue && (argCount == 2)) {
                    return mal::nilValue();
                }
                return EVAL(list->item(isTrue ? 2 : 3), env);
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

static const char* malFunctionTable[] = {
    "(def! not (fn* (cond) (if cond false true)))",
};

static void installFunctions(malEnvPtr env) {
    for (auto &function : malFunctionTable) {
        rep(function, env);
    }
}
