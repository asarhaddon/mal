class Mal.BuiltinFunctionEval : Mal.BuiltinFunction {
    public weak Mal.Env env;
    public BuiltinFunctionEval(Mal.Env env_) { env = env_; }
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionEval(env);
    }
    public override string name() { return "eval"; }
    public override Mal.Val call(Mal.Val[] args) throws Mal.Error {
        check_arg_count(1, args);
        return Mal.Main.EVAL(args[0], env);
    }
    public override void gc_traverse() {
        base.gc_traverse();
        env.visit();
    }
}

class Mal.Main : GLib.Object {
    static bool eof;

    static construct {
        eof = false;
    }

    public static void check_args(string name, uint expected,
                                  GLib.List<weak Mal.Val> got) throws Mal.Error {
        if (got.length() != expected) {
            string s = "";
            foreach (var x in got)
                s += " " + pr_str(x, true);
            throw new Mal.Error.BAD_PARAMS("%s: expected %u argument(s), got:%s",
                                           name, expected, s);
        }
    }

    public static Mal.Val? READ() {
        string? line = Readline.readline("user> ");
        if (line != null) {
            if (line.length > 0)
                Readline.History.add(line);

            try {
                return Reader.read_str(line);
            } catch (Mal.Error err) {
                Mal.BuiltinFunctionThrow.clear();
                GLib.stderr.printf("%s\n", err.message);
                return null;
            }
        } else {
            stdout.printf("\n");
            eof = true;
            return null;
        }
    }

    private static Mal.Val define_eval(Mal.Val key, Mal.Val value,
                                       Mal.Env env,
                                       string context)
    throws Mal.Error {
        var symkey = key as Mal.Sym;
        if (symkey == null)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a symbol to define", context);
        var val = EVAL(value, env);
        env.set(symkey.v, val);
        return val;
    }

    //  If ast is (sym x), return x, else return null.
    public static Mal.Val? unquoted (Mal.Val ast,
                                     string sym)
    throws Mal.Error {
        var list = ast as Mal.List;
        if (list == null || list.vs == null) return null;
        var a0 = list.vs.data as Mal.Sym;
        if (a0 == null || a0.v != sym) return null;
        check_args(sym, 1, list.vs.next);
        return list.vs.next.data;
    }

    public static Mal.Val qq_loop(Mal.Val elt,
                                  Mal.Val acc)
    throws Mal.Error {
        var list = new Mal.List.empty();
        var unq = unquoted(elt, "splice-unquote");
        if (unq != null) {
            list.vs.append(new Mal.Sym("concat"));
            list.vs.append(unq);
        } else {
            list.vs.append(new Mal.Sym("cons"));
            list.vs.append(quasiquote (elt));
        }
        list.vs.append(acc);
        return list;
    }

    public static Mal.Val qq_foldr(Mal.Iterator xs)
    throws Mal.Error {
        if (xs.empty()) {
            return new Mal.List.empty();
        } else {
            var elt = xs.deref();
            xs.step();
            return qq_loop(elt, qq_foldr(xs));
        }
    }

    public static Mal.Val quasiquote(Mal.Val ast)
    throws Mal.Error {
        var lst  = ast as Mal.List;
        if (lst != null) {
            var unq = unquoted(ast, "unquote");
            if (unq != null) {
                return unq;
            } else {
                return qq_foldr(lst.iter());
            }
        }
        var vec = ast as Mal.Vector;
        if (vec != null) {
            var list = new Mal.List.empty();
            list.vs.append(new Mal.Sym("vec"));
            list.vs.append(qq_foldr(vec.iter()));
            return list;
        } else if (ast is Mal.Sym || ast is Mal.Hashmap) {
            var list = new Mal.List.empty();
            list.vs.append(new Mal.Sym("quote"));
            list.vs.append(ast);
            return list;
        } else {
            return ast;
        }
    }

    public static Mal.Val EVAL(Mal.Val ast_, Mal.Env env_)
    throws Mal.Error {
        // Copy the implicitly 'unowned' function arguments into
        // ordinary owned variables which increment the objects'
        // reference counts. This is so that when we overwrite these
        // variables within the loop (for TCO) the objects we assign
        // into them don't immediately get garbage-collected.
        Mal.Val ast = ast_;
        Mal.Env env = env_;
        while (true) {
            GC.Core.maybe_collect();

            var dbgeval = env.get("DEBUG-EVAL");
            if (dbgeval != null && dbgeval.truth_value())
                stdout.printf("EVAL: %s\n", pr_str(ast));

            var key = ast as Mal.Sym;
            if (key != null) {
                var val = env.get(key.v);
                if (val == null)
                    throw new Error.ENV_LOOKUP_FAILED("'%s' not found", key.v);
                return val;
            }
            var vec = ast as Mal.Vector;
            if (vec != null) {
                var result = new Mal.Vector.with_size(vec.length);
                for (var i = 0; i < vec.length; i++)
                    result[i] = EVAL(vec[i], env);
                return result;
            }
            var ast_as_map = ast as Mal.Hashmap;
            if (ast_as_map != null) {
                var result = new Mal.Hashmap();
                var map = ast_as_map.vs;
                foreach (var k in map.get_keys())
                    result.insert(k, EVAL(map[k], env));
                return result;
            }
            var ast_as_list = ast as Mal.List;
            if (ast_as_list != null) {
                unowned var list = ast_as_list.vs;
                if (list == null)
                    return ast;

                var first = list.data;
                list = list.next;

                var sym = first as Mal.Sym;
                if (sym != null) {
                    switch (sym.v) {
                    case "def!":
                        check_args("def!", 2, list);
                        return define_eval(list.data, list.next.data, env, "def!");
                    case "defmacro!":
                        check_args("defmacro!", 2, list);
                        var symkey = list.data as Mal.Sym;
                        if (symkey == null)
                            throw new Mal.Error.BAD_PARAMS(
                                "defmacro!: expects a symbol");
                        var val = EVAL(list.next.data, env) as Mal.Function;
                        if (val == null)
                            throw new Mal.Error.BAD_PARAMS(
                                "defmacro!: expected a function");
                        val = val.copy() as Mal.Function;
                        val.is_macro = true;
                        env.set(symkey.v, val);
                        return val;
                    case "let*":
                        check_args("let*", 2, list);
                        var defns = list.data as Mal.Listlike;
                        env = new Mal.Env.within(env);

                        if (defns != null) {
                            for (var i = defns.iter(); i.nonempty(); i.step()) {
                                var k = i.deref();
                                if (i.step().empty())
                                    throw new Mal.Error.BAD_PARAMS(
                                        "let*: expected an even-length list" +
                                        " of definitions");
                                define_eval(k, i.deref(), env, "let*");
                            }
                        } else {
                            throw new Mal.Error.BAD_PARAMS(
                                "let*: expected a list or vector of definitions");
                        }
                        ast = list.next.data;
                        continue;      // tail-call optimisation
                    case "do":
                        if (list == null)
                            throw new Mal.Error.BAD_PARAMS(
                                "do: expected at least one argument");
                        while(list.next != null) {
                            EVAL(list.data, env);
                            list = list.next;
                        }
                        ast = list.data;
                        continue; // tail-call optimization
                    case "if":
                        if (list.length() != 2 && list.length() != 3)
                            throw new Mal.Error.BAD_PARAMS(
                                "if: expected two or three arguments");
                        var cond = EVAL(list.data, env);
                        list = list.next;
                        if (!cond.truth_value()) {
                            // Skip to the else clause, which defaults to nil.
                            list = list.next;
                            if (list == null)
                                return new Mal.Nil();
                        }
                        ast = list.data;
                        continue;      // tail-call optimisation
                    case "fn*":
                        check_args("fn*", 2, list);
                        var body = list.next.data;
                        Mal.Iterator iter;
                        string[] binds_s;
                        var binds_lst = list.data as Mal.List;
                        var binds_vec = list.data as Mal.Vector;
                        if (binds_lst != null) {
                            binds_s = new string[binds_lst.vs.length()];
                            iter = binds_lst.iter();
                        } else if (binds_vec != null) {
                            binds_s = new string[binds_vec.length];
                            iter = binds_vec.iter();
                        } else
                            throw new Mal.Error.BAD_PARAMS(
                                "fn*: expected a list of parameter names");
                        for (uint i = 0; i < binds_s.length;  ++i) {
                            var s = iter.deref() as Mal.Sym;
                            iter.step();
                            if (s == null)
                                throw new Mal.Error.BAD_PARAMS(
                                    "fn*: expected parameter name to be "+
                                    "symbol");
                            binds_s[i] = s.v;
                        }
                        return new Mal.Function(binds_s, body, env);
                    case "quote":
                        check_args("quote", 1, list);
                        return list.data;
                    case "quasiquote":
                        check_args("quasiquote", 1, list);
                        ast = quasiquote(list.data);
                        continue;      // tail-call optimisation
                    case "try*":
                        if (list.length() != 1 && list.length() != 2)
                            throw new Mal.Error.BAD_PARAMS(
                                "try*: expected one or two arguments");
                        var trybody = list.data;
                        if (list.length() == 1) {
                            // Trivial catchless form of try
                            ast = trybody;
                            continue;  // tail-call optimisation
                        }
                        var catchclause = list.next.data as Mal.List;
                        var catch_as_sym = catchclause.vs.data as Mal.Sym;
                        if (catch_as_sym == null || catch_as_sym.v != "catch*")
                            throw new Mal.Error.BAD_PARAMS(
                                "try*: expected catch*");
                        check_args("catch*", 2, catchclause.vs.next);
                        var catchparam = catchclause.vs.next.data as Mal.Sym;
                        if (catchparam == null)
                            throw new Mal.Error.BAD_PARAMS(
                                "catch*: expected a parameter name");
                        var catchbody = catchclause.vs.next.next.data;
                        try {
                            return EVAL(trybody, env);
                        } catch (Mal.Error exc) {
                            var catchenv = new Mal.Env.within(env);
                            catchenv.set(catchparam.v, Mal.BuiltinFunctionThrow.
                                         thrown_value(exc));
                            ast = catchbody;
                            env = catchenv;
                            continue;  // tail-call optimisation
                        }
                    }
                }

                Mal.Val firstdata = EVAL(first, env);
                var newlist = new Mal.Val[list.length()];

                var bf = firstdata as Mal.BuiltinFunction;
                if (bf != null) {
                    uint i = 0;
                    foreach (var x in list)
                        newlist[i++] = EVAL(x, env);
                    return bf.call(newlist);
                }
                var fn = firstdata as Mal.Function;
                if (fn != null) {
                    if (fn.is_macro) {
                        uint i = 0;
                        foreach (var x in list)
                            newlist[i++] = x;
                        var fenv = new Mal.Env.funcall(fn.env, fn.parameters, newlist);
                        ast = EVAL(fn.body, fenv);
                        continue;
                    }
                    uint i = 0;
                    foreach (var x in list)
                        newlist[i++] = EVAL(x, env);
                    env = new Mal.Env.funcall(fn.env, fn.parameters, newlist);
                    ast = fn.body;
                    continue;      // tail-call optimisation
                } else {
                    throw new Mal.Error.CANNOT_APPLY(
                        "bad value at start of list");
                }
            } else {
                return ast;
            }
        }
    }

    public static void PRINT(Mal.Val value) {
        stdout.printf("%s\n", pr_str(value));
    }

    public static void rep(Mal.Env env) throws Mal.Error {
        Mal.Val? val = READ();
        if (val != null) {
            val = EVAL(val, env);
            PRINT(val);
        }
    }

    public static void setup(string line, Mal.Env env) {
        try {
            EVAL(Reader.read_str(line), env);
        } catch (Mal.Error err) {
            stderr.printf("Error during setup:\n%s\n-> %s\n",
                          line, err.message);
            GLib.Process.exit(1);
        }
    }

    public static int main(string[] args) {
        var env = new Mal.Env();

        Mal.Core.make_ns(env);
        env.set("eval", new Mal.BuiltinFunctionEval(env));

        setup("(def! not (fn* (a) (if a false true)))", env);
        setup("(def! load-file (fn* (f) (eval (read-string (str \"(do \" (slurp f) \"\nnil)\")))))", env);
        setup("(defmacro! cond (fn* (& xs) (if (> (count xs) 0) (list 'if (first xs) (if (> (count xs) 1) (nth xs 1) (throw \"odd number of forms to cond\")) (cons 'cond (rest (rest xs)))))))", env);

        var ARGV = new GLib.List<Mal.Val>();
        for (int i = 2; i < args.length; ++i)
            ARGV.append(new Mal.String(args[i]));
        env.set("*ARGV*", new Mal.List(ARGV));
        ARGV = null; // (def! *ARGV* 0) should deallocate the strings.

        if (args.length > 1) {
            setup("(load-file \"%s\")".printf(args[1]), env);
        } else {
            while (!eof) {
                try {
                    rep(env);
                } catch (Mal.Error.EXCEPTION_THROWN exc) {
                    GLib.stderr.printf(
                        "uncaught exception: %s\n",
                        pr_str(Mal.BuiltinFunctionThrow.thrown_value(exc)));
                } catch (Mal.Error err) {
                    GLib.stderr.printf("%s\n", err.message);
                }
            }
        }

#if GC_STATS
        stdout.printf("The final object count should be 0\n.");
        env = null;
        GC.Core.collect();
#endif

        return 0;
    }
}
