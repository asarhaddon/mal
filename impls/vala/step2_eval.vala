abstract class Mal.BuiltinFunctionDyadicArithmetic : Mal.BuiltinFunction {
    public abstract int64 result(int64 a, int64 b);
    public override Mal.Val call(Mal.Val[] args) throws Mal.Error {
        check_arg_count(2, args);
        Mal.Num a = args[0] as Mal.Num;
        Mal.Num b = args[1] as Mal.Num;
        if (a == null || b == null)
            throw new Mal.Error.BAD_PARAMS("%s: expected two numbers", name());
        return new Mal.Num(result(a.v, b.v));
    }
}

class Mal.BuiltinFunctionAdd : Mal.BuiltinFunctionDyadicArithmetic {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionAdd();
    }
    public override string name() { return "+"; }
    public override int64 result(int64 a, int64 b) { return a+b; }
}

class Mal.BuiltinFunctionSub : Mal.BuiltinFunctionDyadicArithmetic {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionSub();
    }
    public override string name() { return "-"; }
    public override int64 result(int64 a, int64 b) { return a-b; }
}

class Mal.BuiltinFunctionMul : Mal.BuiltinFunctionDyadicArithmetic {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionMul();
    }
    public override string name() { return "*"; }
    public override int64 result(int64 a, int64 b) { return a*b; }
}

class Mal.BuiltinFunctionDiv : Mal.BuiltinFunctionDyadicArithmetic {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionDiv();
    }
    public override string name() { return "/"; }
    public override int64 result(int64 a, int64 b) { return a/b; }
}

class Mal.Main : GLib.Object {
    static bool eof;

    static construct {
        eof = false;
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

    public static Mal.Val EVAL(Mal.Val ast, GLib.HashTable<string, Mal.Val> env)
    throws Mal.Error {

            GC.Core.maybe_collect();

        //  stdout.printf("EVAL: %s\n", pr_str(ast));

            var key = ast as Mal.Sym;
            if (key != null) {
                var val = env[key.v];
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

                Mal.Val firstdata = EVAL(first, env);
                var newlist = new Mal.Val[list.length()];

                var bf = firstdata as Mal.BuiltinFunction;
                if (bf != null) {
                    uint i = 0;
                    foreach (var x in list)
                        newlist[i++] = EVAL(x, env);
                    return bf.call(newlist);
                } else {
                    throw new Mal.Error.CANNOT_APPLY(
                        "bad value at start of list");
                }
            } else {
                return ast;
            }
    }

    public static void PRINT(Mal.Val value) {
        stdout.printf("%s\n", pr_str(value));
    }

    public static void rep(GLib.HashTable<string, Mal.Val> env) throws Mal.Error {
        Mal.Val? val = READ();
        if (val != null) {
            val = EVAL(val, env);
            PRINT(val);
        }
    }

    public static int main(string[] args) {
        var env = new GLib.HashTable<string, Mal.Val>(str_hash, str_equal);

        env["+"] = new BuiltinFunctionAdd();
        env["-"] = new BuiltinFunctionSub();
        env["*"] = new BuiltinFunctionMul();
        env["/"] = new BuiltinFunctionDiv();

        while (!eof) {
            try {
                rep(env);
            } catch (Mal.Error err) {
                GLib.stderr.printf("%s\n", err.message);
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
