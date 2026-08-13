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
//  Installs functions and macros implemented in MAL.

String rep(const String& input, malEnvPtr env);
malValuePtr EVAL(malValuePtr ast, malEnvPtr env);

static void makeArgv(malEnvPtr env, int argc, char* argv[]);
static malValuePtr quasiquote(malValuePtr obj);

const malEnvPtr replEnv(new malEnv);

int main(int argc, char* argv[])
{
    String prompt = "user> ";
    String input;
    installCore();
    installFunctions(replEnv);
    makeArgv(replEnv, argc - 2, argv + 2);
    if (argc > 1) {
        String filename = escape(argv[1]);
        rep(STRF("(load-file %s)", filename.c_str()), replEnv);
        return 0;
    }
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

static void makeArgv(malEnvPtr env, int argc, char* argv[])
{
    malValueVec* args = new malValueVec();
    for (int i = 0; i < argc; i++) {
        args->push_back(mal::string(argv[i]));
    }
    env->set("*ARGV*", mal::list(args));
}

malValuePtr READ(const String& input)
{
    return readStr(input);
}

malValuePtr EVAL(malValuePtr ast, malEnvPtr env)
{
    while (1) {

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

            if (special == "defmacro!") {
                checkArgsIs("defmacro!", 2, argCount);

                const malSymbol* id = VALUE_CAST("defmacro!", malSymbol, list->item(1));
                malValuePtr body = EVAL(list->item(2), env);
                const malLambda* lambda = VALUE_CAST("defmacro!", malLambda, body);
                return env->set(id->value(), mal::macro(*lambda));
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
                ast = list->item(isTrue ? 2 : 3);
                continue; // TCO
            }

            if (special == "let*") {
                checkArgsIs("let*", 2, argCount);
                const malSequence* bindings =
                    VALUE_CAST("let*", malSequence, list->item(1));
                int count = bindings->count();
                checkArgsEven("let*", count);
                malEnvPtr inner(new malEnv(env));
                for (int i = 0; i < count; i += 2) {
                    const malSymbol* var =
                        VALUE_CAST("let*", malSymbol, bindings->item(i));
                    inner->set(var->value(), EVAL(bindings->item(i+1), inner));
                }
                ast = list->item(2);
                env = inner;
                continue; // TCO
            }

            if (special == "quasiquote") {
                checkArgsIs("quasiquote", 1, argCount);
                ast = quasiquote(list->item(1));
                continue; // TCO
            }

            if (special == "quote") {
                checkArgsIs("quote", 1, argCount);
                return list->item(1);
            }
        }

        // Now we're left with the case of a regular list to be evaluated.
        auto op = VALUE_CAST("EVAL apply phase", malApplicable,
                             EVAL(list->item(0), env));
        auto lambda = dynamic_cast<malLambda*>(op);
        if (lambda && lambda->isMacro()) {
            ast = lambda->apply(list->begin()+1, list->end());
            continue; // TCO
        }
        malValueVec items;
        for (auto i = list->begin() + 1, e = list->end(); i != e; ++i) {
            items.push_back(EVAL(*i, env));
        }
        if (lambda) {
            ast = lambda->getBody();
            env = new malEnv(lambda->getEnv(), lambda->getBindings(),
                             items.begin(), items.end());
            continue; // TCO
        }
        return op->apply(items.begin(), items.end());
    }
}

String PRINT(malValuePtr ast)
{
    return ast->print(true);
}

static bool isSymbol(malValuePtr obj, const String& text)
{
    const malSymbol* sym = DYNAMIC_CAST(malSymbol, obj);
    return sym && (sym->value() == text);
}

//  Return arg when ast matches ('sym, arg), else NULL.
static malValuePtr starts_with(const malValuePtr ast, const char* sym)
{
    const malList* list = DYNAMIC_CAST(malList, ast);
    if (!list || list->isEmpty() || !isSymbol(list->item(0), sym))
        return NULL;
    checkArgsIs(sym, 1, list->count() - 1);
    return list->item(1);
}

static malValuePtr quasiquote(malValuePtr obj)
{
    if (DYNAMIC_CAST(malSymbol, obj) || DYNAMIC_CAST(malHash, obj))
        return mal::list(mal::symbol("quote"), obj);

    const malSequence* seq = DYNAMIC_CAST(malSequence, obj);
    if (!seq)
        return obj;

    const malValuePtr unquoted = starts_with(obj, "unquote");
    if (unquoted)
        return unquoted;

    malValuePtr res = mal::list(new malValueVec(0));
    for (int i=seq->count()-1; 0<=i; i--) {
        const malValuePtr elt     = seq->item(i);
        const malValuePtr spl_unq = starts_with(elt, "splice-unquote");
        if (spl_unq)
            res = mal::list(mal::symbol("concat"), spl_unq, res);
         else
            res = mal::list(mal::symbol("cons"), quasiquote(elt), res);
    }
    if (DYNAMIC_CAST(malVector, obj))
        res = mal::list(mal::symbol("vec"), res);
    return res;
}

static const char* malFunctionTable[] = {
    "(defmacro! cond (fn* (& xs) (if (> (count xs) 0) (list 'if (first xs) (if (> (count xs) 1) (nth xs 1) (throw \"odd number of forms to cond\")) (cons 'cond (rest (rest xs)))))))",
    "(def! not (fn* (cond) (if cond false true)))",
    "(def! load-file (fn* (filename) \
        (eval (read-string (str \"(do \" (slurp filename) \"\nnil)\")))))",
};

static void installFunctions(malEnvPtr env) {
    for (auto &function : malFunctionTable) {
        rep(function, env);
    }
}
