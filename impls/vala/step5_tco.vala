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
                    }
                }

                Mal.Val firstdata = EVAL(first, env);
                var newlist = new Mal.Val[list.length()];

                var bf = firstdata as Mal.BuiltinFunction;
                if (bf != null) {
                    uint i = 0;
                    foreach (var x in list)
                        newlist[i++] = EVAL(x, env);
                    return bf.call(newlist, bf.name);
                }
                var fn = firstdata as Mal.Function;
                if (fn != null) {
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

        setup("(def! not (fn* (a) (if a false true)))", env);

        while (!eof) {
            try {
                rep(env);
            } catch (Mal.Error err) {
                GLib.stderr.printf(
                    "uncaught exception: %s\n",
                    err.message);
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
