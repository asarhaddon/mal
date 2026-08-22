#include "MAL.h"

#include "Core.h"
#include "Environment.h"
#include "Reader.h"
#include "ReadLine.h"
#include "Types.h"

#include <iostream>

malValuePtr READ(const String& input);
String PRINT(malValuePtr ast);
static void installFunctions(malEnvPtr env);
String rep(const String& input, malEnvPtr env);

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
    while (1) {

       const malEnvPtr dbgenv = env->find("DEBUG-EVAL");
       if (dbgenv && dbgenv->get("DEBUG-EVAL")->isTrue()) {
           std::cout << "EVAL: " << PRINT(ast) << "\n";
       }

        const malList* list = DYNAMIC_CAST(malList, ast);
        if (!list || (list->count() == 0)) {
            return ast->eval(env);
        }

        // From here on down we are evaluating a non-empty list.
        // First handle the special forms.
        if (const malSymbol* symbol = DYNAMIC_CAST(malSymbol, list->item(0))) {
            String special = symbol->value();
            int argCount = list->count() - 1;

            if (special == "def!") {
                checkArgsIs("def!", 2, argCount);
                const malSymbol* id = VALUE_CAST(malSymbol, list->item(1));
                return env->set(id->value(), EVAL(list->item(2), env));
            }

            if (special == "do") {
                checkArgsAtLeast("do", 1, argCount);

                for (int i = 1; i < argCount; i++) {
                    EVAL(list->item(i), env);
                }
                ast = list->item(argCount);
                continue; // TCO
            }

            if (special == "fn*") {
                checkArgsIs("fn*", 2, argCount);

                const malSequence* bindings =
                    VALUE_CAST(malSequence, list->item(1));
                StringVec params;
                for (int i = 0; i < bindings->count(); i++) {
                    const malSymbol* sym =
                        VALUE_CAST(malSymbol, bindings->item(i));
                    params.push_back(sym->value());
                }

                return mal::lambda(params, list->item(2), env);
            }

            if (special == "if") {
                checkArgsBetween("if", 2, 3, argCount);

                bool isTrue = EVAL(list->item(1), env)->isTrue();
                if (!isTrue && (argCount == 2)) {
                    return mal::nilValue();
                }
                ast = list->item(isTrue ? 2 : 3);
                continue; // TCO
            }

            if (special == "let*") {
                checkArgsIs("let*", 2, argCount);
                const malSequence* bindings =
                    VALUE_CAST(malSequence, list->item(1));
                int count = checkArgsEven("let*", bindings->count());
                malEnvPtr inner(new malEnv(env));
                for (int i = 0; i < count; i += 2) {
                    const malSymbol* var =
                        VALUE_CAST(malSymbol, bindings->item(i));
                    inner->set(var->value(), EVAL(bindings->item(i+1), inner));
                }
                ast = list->item(2);
                env = inner;
                continue; // TCO
            }
        }

        // Now we're left with the case of a regular list to be evaluated.
        auto op = VALUE_CAST(malApplicable, EVAL(list->item(0), env));
        auto lambda = dynamic_cast<malLambda*>(op);
        malValueVec items;
        for (auto i = list->begin() + 1, e = list->end(); i != e; ++i) {
            items.push_back(EVAL(*i, env));
        }
        if (lambda) {
            ast = lambda->getBody();
            env = lambda->makeEnv(items.begin(), items.end());
            continue; // TCO
        }
        return op->apply(items.begin(), items.end());
    }
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
