#include "MAL.h"

#include "Environment.h"
#include "ReadLine.h"
#include "Types.h"

#include <iostream>
#include <memory>

malValuePtr READ(const String& input);
String PRINT(malValuePtr ast);
static void installFunctions(malEnvPtr env);
//  Installs functions and macros implemented in MAL.

static void makeArgv(malEnvPtr env, int argc, char* argv[]);
static String safeRep(const String& input, malEnvPtr env);
static malValuePtr quasiquote(const malValuePtr ast, malEnvPtr env);
static malValuePtr macroExpand(malValuePtr obj, malEnvPtr env);

static ReadLine s_readLine("~/.mal-history");

static malEnvPtr replEnv(new malEnv);

int main(int argc, char* argv[])
{
    String prompt = "user> ";
    String input;
    installCore(replEnv);
    installFunctions(replEnv);
    makeArgv(replEnv, argc - 2, argv + 2);
    if (argc > 1) {
        String filename = escape(argv[1]);
        safeRep(STRF("(load-file %s)", filename.c_str()), replEnv);
        return 0;
    }
    while (s_readLine.get(prompt, input)) {
        String out = safeRep(input, replEnv);
        if (out.length() > 0)
            std::cout << out << "\n";
    }
    return 0;
}

static String safeRep(const String& input, malEnvPtr env)
{
    try {
        return rep(input, env);
    }
    catch (malEmptyInputException&) {
        return String();
    }
    catch (String& s) {
        return s;
    };
}

static void makeArgv(malEnvPtr env, int argc, char* argv[])
{
    malValueVec* args = new malValueVec();
    for (int i = 0; i < argc; i++) {
        args->push_back(mal::string(argv[i]));
    }
    env->set("*ARGV*", mal::list(args));
}

String rep(const String& input, malEnvPtr env)
{
    return PRINT(EVAL(READ(input), env));
}

malValuePtr READ(const String& input)
{
    return readStr(input);
}

malValuePtr EVAL(malValuePtr ast, malEnvPtr env)
{
    if (!env) {
        env = replEnv;
    }
    while (1) {
        const malList* list = DYNAMIC_CAST(malList, ast);
        if (!list || (list->count() == 0)) {
            return ast->eval(env);
        }

        ast = macroExpand(ast, env);
        list = DYNAMIC_CAST(malList, ast);
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

            if (special == "defmacro!") {
                checkArgsIs("defmacro!", 2, argCount);

                const malSymbol* id = VALUE_CAST(malSymbol, list->item(1));
                malValuePtr body = EVAL(list->item(2), env);
                const malLambda* lambda = VALUE_CAST(malLambda, body);
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

            if (special == "macroexpand") {
                checkArgsIs("macroexpand", 1, argCount);
                return macroExpand(list->item(1), env);
            }

            if (special == "quasiquote") {
                checkArgsIs("quasiquote", 1, argCount);
                return quasiquote(list->item(1), env);
            }

            if (special == "quote") {
                checkArgsIs("quote", 1, argCount);
                return list->item(1);
            }
        }

        // Now we're left with the case of a regular list to be evaluated.
        std::unique_ptr<malValueVec> items(list->evalItems(env));
        malValuePtr op = items->at(0);
        if (const malLambda* lambda = DYNAMIC_CAST(malLambda, op)) {
            ast = lambda->getBody();
            env = lambda->makeEnv(items->begin()+1, items->end());
            continue; // TCO
        }
        else {
            return APPLY(op, items->begin()+1, items->end());
        }
    }
}

String PRINT(malValuePtr ast)
{
    return ast->print(true);
}

malValuePtr APPLY(malValuePtr op, malValueIter argsBegin, malValueIter argsEnd)
{
    const malApplicable* handler = DYNAMIC_CAST(malApplicable, op);
    MAL_CHECK(handler != NULL,
              "\"%s\" is not applicable", op->print(true).c_str());

    return handler->apply(argsBegin, argsEnd);
}

//  Return arg when ast matches ('sym, arg), else NULL.
static malValuePtr starts_with(const malValuePtr ast, const char* sym)
{
    const malList* list = DYNAMIC_CAST(malList, ast);
    if (!list || list->isEmpty())
        return NULL;
    const malSymbol* symbol = DYNAMIC_CAST(malSymbol, list->item(0));
    if (!symbol || symbol->value().compare(sym))
        return NULL;
    checkArgsIs(sym, 1, list->count() - 1);
    return list->item(1);
}

static malValuePtr quasiquote(const malValuePtr ast, malEnvPtr env)
{
    const malSequence* seq = DYNAMIC_CAST(malSequence, ast);
    if (!seq)
        return ast;

    const malValuePtr unquoted = starts_with(ast, "unquote");
    if (unquoted)
        return EVAL(unquoted, env);

    malValueVec* res = new malValueVec;
    for (auto elt = seq->begin(); elt != seq->end(); ++elt) {
        const malValuePtr spl_unq = starts_with(*elt, "splice-unquote");
        if (spl_unq) {
            //  FIXME: this causes a segfault in perf.mal:
            // const malList* lst = DYNAMIC_CAST(malList, EVAL(spl_unq, env));
            const malValuePtr evd = EVAL(spl_unq, env);
            const malList* lst = DYNAMIC_CAST(malList, evd);
            for (auto subelt = lst->begin(); subelt != lst->end(); ++subelt)
                res->push_back(*subelt);
        } else
            res->push_back(quasiquote(*elt, env));
    }
    if (DYNAMIC_CAST(malList, ast))
        return mal::list(res);
    else
        return mal::vector(res);
}

static const malLambda* isMacroApplication(malValuePtr obj, malEnvPtr env)
{
    const malList* seq = DYNAMIC_CAST(malList, obj);
    if (seq && !seq->isEmpty()) {
        if (malSymbol* sym = DYNAMIC_CAST(malSymbol, seq->item(0))) {
            if (malEnvPtr symEnv = env->find(sym->value())) {
                malValuePtr value = sym->eval(symEnv);
                if (malLambda* lambda = DYNAMIC_CAST(malLambda, value)) {
                    return lambda->isMacro() ? lambda : NULL;
                }
            }
        }
    }
    return NULL;
}

static malValuePtr macroExpand(malValuePtr obj, malEnvPtr env)
{
    while (const malLambda* macro = isMacroApplication(obj, env)) {
        const malSequence* seq = STATIC_CAST(malSequence, obj);
        obj = macro->apply(seq->begin() + 1, seq->end());
    }
    return obj;
}

static const char* malFunctionTable[] = {
    "(defmacro! cond (fn* (& xs) (if (> (count xs) 0) (list 'if (first xs) (if (> (count xs) 1) (nth xs 1) (throw \"odd number of forms to cond\")) (cons 'cond (rest (rest xs)))))))",
    "(def! not (fn* (cond) (if cond false true)))",
    "(def! load-file (fn* (filename) \
        (eval (read-string (str \"(do \" (slurp filename) \")\")))))",
};

static void installFunctions(malEnvPtr env) {
    for (auto &function : malFunctionTable) {
        rep(function, env);
    }
}

// Added to keep the linker happy at step A
malValuePtr readline(const String& prompt)
{
    String input;
    if (s_readLine.get(prompt, input)) {
        return mal::string(input);
    }
    return mal::nilValue();
}

