class Mal.Core {

    private delegate int64 DyadicArithmetic(int64 a, int64 b);
    private static Mal.Val arithmetic2(Mal.Val[] args, string name,
                                       DyadicArithmetic result)
      throws Mal.Error {
        BuiltinFunction.check_arg_count(2, args, name);
        Mal.Num a = args[0] as Mal.Num;
        Mal.Num b = args[1] as Mal.Num;
        if (a == null || b == null)
            throw new Mal.Error.BAD_PARAMS("%s: expected two numbers", name);
        return new Mal.Num(result(a.v, b.v));
    }

    private static Mal.Val Add(Mal.Val[] args, string name) throws Mal.Error {
        return arithmetic2(args, name, (a, b) => { return a+b; });
    }

    private static Mal.Val Sub(Mal.Val[] args, string name) throws Mal.Error {
        return arithmetic2(args, name, (a, b) => { return a-b; });
    }

    private static Mal.Val Mul(Mal.Val[] args, string name) throws Mal.Error {
        return arithmetic2(args, name, (a, b) => { return a*b; });
    }

    private static Mal.Val Div(Mal.Val[] args, string name) throws Mal.Error {
        return arithmetic2(args, name, (a, b) => { return a/b; });
    }

    private static Mal.Val PrStr(Mal.Val[] args, string name) throws Mal.Error {
        string result = pr_list(args, true, " ");
        return new Mal.String(result);
    }

    private static Mal.Val Str(Mal.Val[] args, string name) throws Mal.Error {
        string result = pr_list(args, false, "");
        return new Mal.String(result);
    }

    private static Mal.Val Prn(Mal.Val[] args, string name) throws Mal.Error {
        stdout.printf(pr_list(args, true, " "));
        stdout.printf("\n");
        return new Mal.Nil();
    }

    private static Mal.Val Println(Mal.Val[] args, string name) throws Mal.Error {
        stdout.printf(pr_list(args, false, " "));
        stdout.printf("\n");
        return new Mal.Nil();
    }

    private static Mal.Val ReadString(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        var arg1 = args[0] as Mal.String;
        if (arg1 == null)
            throw new Mal.Error.BAD_PARAMS("%s: expected one string", name);
        return Reader.read_str(arg1.v);
    }

    private static Mal.Val Slurp(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        var arg1 = args[0] as Mal.String;
        if (arg1 == null)
            throw new Mal.Error.BAD_PARAMS("%s: expected one string", name);
        string filename = arg1.v;
        string contents;
        try {
            FileUtils.get_contents(filename, out contents);
        } catch (FileError e) {
            throw new Mal.Error.BAD_PARAMS("%s: unable to read '%s': %s",
                                           name, filename, e.message);
        }
        return new Mal.String(contents);
    }

    private static Mal.Val FnList(Mal.Val[] args, string name) throws Mal.Error {
        var result = new Mal.List.empty();
        foreach (var x in args)
            result.vs.append(x);
        return result;
    }

    private static Mal.Val ListP(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        return new Mal.Bool(args[0] is Mal.List);
    }

    private static Mal.Val SequentialP(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        return new Mal.Bool(args[0] is Mal.List ||
                            args[0] is Mal.Vector);
    }

    private static Mal.Val NilP(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        return new Mal.Bool(args[0] is Mal.Nil);
    }

    private static Mal.Val TrueP(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        var arg1 = args[0] as Mal.Bool;
        return new Mal.Bool(arg1 != null && arg1.v);
    }

    private static Mal.Val FalseP(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        var arg1 = args[0] as Mal.Bool;
        return new Mal.Bool(arg1 != null && !arg1.v);
    }

    private static Mal.Val NumberP(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        return new Mal.Bool(args[0] is Mal.Num);
    }

    private static Mal.Val StringP(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        return new Mal.Bool(args[0] is Mal.String);
    }

    private static Mal.Val SymbolP(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        return new Mal.Bool(args[0] is Mal.Sym);
    }

    private static Mal.Val KeywordP(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        return new Mal.Bool(args[0] is Mal.Keyword);
    }

    private static Mal.Val FnVector(Mal.Val[] args, string name) throws Mal.Error {
        var result = new Mal.Vector.with_size(args.length);
        uint i = 0;
        foreach (var value in args)
            result[i++] = value;
        return result;
    }

    private static Mal.Val VectorP(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        return new Mal.Bool(args[0] is Mal.Vector);
    }

    private static Mal.Val HashMap(Mal.Val[] args, string name) throws Mal.Error {
        var map = new Mal.Hashmap();
        if (args.length % 2 != 0)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected an even number of arguments", name);
        for (uint i = 0; i < args.length; i += 2) {
            var key = args[i];
            var value = args[i+1];
            map.insert(key, value);
        }
        return map;
    }

    private static Mal.Val MapP(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        return new Mal.Bool(args[0] is Mal.Hashmap);
    }

    private static Mal.Val EmptyP(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        var list = args[0] as Mal.Listlike;
        if (list == null)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a list-like argument", name);
        return new Mal.Bool(list.iter().deref() == null);
    }

    private static Mal.Val FnP(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        if (args[0] is Mal.BuiltinFunction)
            return new Mal.Bool(true);
        var fn = args[0] as Mal.Function;
        return new Mal.Bool(fn != null && !fn.is_macro);
    }

    private static Mal.Val MacroP(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        var fn = args[0] as Mal.Function;
        return new Mal.Bool(fn != null && fn.is_macro);
    }

    private static Mal.Val Count(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        if (args[0] is Mal.Nil)
            return new Mal.Num(0);     // nil is treated like ()
        var l = args[0] as Mal.List;
        if (l != null)
            return new Mal.Num(l.vs.length());
        var v = args[0] as Mal.Vector;
        if (v != null)
            return new Mal.Num(v.length);
        throw new Mal.Error.BAD_PARAMS(
            "%s: expected a list argument", name);
    }

    private static bool eq(Mal.Val a, Mal.Val b) {
        if (a is Mal.Nil && b is Mal.Nil)
            return true;
        var abool = a as Mal.Bool;
        if (abool != null) {
            var bbool = b as Mal.Bool;
            return bbool != null && abool.v == bbool.v;
        }
        var asym = a as Mal.Sym;
        if (asym != null) {
            var bsym = b as Mal.Sym;
            return bsym != null && asym.v == bsym.v;
        }
        var akwd = a as Mal.Keyword;
        if (akwd != null) {
            var bkwd = b as Mal.Keyword;
            return bkwd != null && akwd.v == bkwd.v;
        }
        var anum = a as Mal.Num;
        if (anum != null) {
            var bnum = b as Mal.Num;
            return bnum != null && anum.v == bnum.v;
        }
        var astr = a as Mal.String;
        if (astr != null) {
            var bstr = b as Mal.String;
            return bstr != null && astr.v == bstr.v;
        }
        var aseq = a as Mal.Listlike; // Nil has already been tested.
        if (aseq != null) {
            if (aseq is Mal.Nil)
                return b is Mal.Nil;
            var bseq = b as Mal.Listlike;
            if (bseq == null || bseq is Mal.Nil)
                return false;
            var aiter = aseq.iter();
            var biter = bseq.iter();
            while (aiter.nonempty() || biter.nonempty()) {
                if (aiter.empty() || biter.empty())
                    return false;
                if (!eq(aiter.deref(), biter.deref()))
                    return false;
                aiter.step();
                biter.step();
            }
            return true;
        }
        var amap = a as Mal.Hashmap;
        if (a != null) {
            var bmap = b as Mal.Hashmap;
            if (bmap == null)
                return false;
            var ah = amap.vs;
            var bh = bmap.vs;
            if (ah.length != bh.length)
                return false;
            foreach (var k in ah.get_keys()) {
                var av = ah[k];
                var bv = bh[k];
                if (bv == null || !eq(av, bv))
                    return false;
            }
            return true;
        }
        return false;
    }
    private static Mal.Val EQ(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(2, args, name);
        return new Mal.Bool(eq(args[0], args[1]));
    }

    private delegate bool NumberCmp(int64 a, int64 b);
    private static Mal.Val MalBuiltinFunctionNumberCmp(
        Mal.Val[] args, string name, NumberCmp result)
      throws Mal.Error {
        BuiltinFunction.check_arg_count(2, args, name);
        Mal.Num a = args[0] as Mal.Num;
        Mal.Num b = args[1] as Mal.Num;
        if (a == null || b == null)
            throw new Mal.Error.BAD_PARAMS("%s: expected two numbers", name);
        return new Mal.Bool(result(a.v, b.v));
    }

    private static Mal.Val LT(Mal.Val[] args, string name) throws Mal.Error {
        return MalBuiltinFunctionNumberCmp(args, name,
                                           (a, b) => { return a<b; });
    }

    private static Mal.Val LE(Mal.Val[] args, string name) throws Mal.Error {
        return MalBuiltinFunctionNumberCmp(args, name,
                                           (a, b) => { return a<=b; });
    }

    private static Mal.Val GT(Mal.Val[] args, string name) throws Mal.Error {
        return MalBuiltinFunctionNumberCmp(args, name,
                                           (a, b) => { return a>b; });
    }

    private static Mal.Val GE(Mal.Val[] args, string name) throws Mal.Error {
        return MalBuiltinFunctionNumberCmp(args, name,
                                           (a, b) => { return a>=b; });
    }

    private static Mal.Val FnAtom(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        return new Mal.Atom(args[0]);
    }

    private static Mal.Val AtomP(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        return new Mal.Bool(args[0] is Mal.Atom);
    }

    private static Mal.Val Deref(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        var atom = args[0] as Mal.Atom;
        if (atom == null)
            throw new Mal.Error.BAD_PARAMS("%s: expected an atom", name);
        return atom.v;
    }

    private static Mal.Val Reset(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(2, args, name);
        var atom = args[0] as Mal.Atom;
        if (atom == null)
            throw new Mal.Error.BAD_PARAMS("%s: expected an atom", name);
        atom.v = args[1];
        return atom.v;
    }

    private static Mal.Val call_function(Mal.Val function, Mal.Val[] fnargs,
                                         string caller) throws Mal.Error {
    var bf = function as Mal.BuiltinFunction;
    if (bf != null)
        return bf.call(fnargs, caller);
    var fn = function as Mal.Function;
    if (fn != null) {
        var env = new Mal.Env.funcall(fn.env, fn.parameters, fnargs);
        return Mal.Main.EVAL(fn.body, env);
    } else {
        throw new Mal.Error.CANNOT_APPLY("%s: expected a function", caller);
    }
    }

    private static Mal.Val Swap(Mal.Val[] args, string name) throws Mal.Error {
        if (args.length < 2)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected at least two arguments", name);
        var atom = args[0] as Mal.Atom;
        if (atom == null)
            throw new Mal.Error.BAD_PARAMS("%s: expected an atom", name);
        var function = args[1];
        var fnargs = new Mal.Val[args.length - 1];
        fnargs[0] = atom.v;
        for (uint i = 2; i < args.length; ++i)
            fnargs[i-1] = args[i];
        atom.v = call_function(function, fnargs, name);
        return atom.v;
    }

    private static Mal.Val Cons(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(2, args, name);
        var first = args[0];
        var rest = args[1] as Mal.Listlike;
        if (rest == null) {
            throw new Mal.Error.BAD_PARAMS("%s: expected a list", name);
        }
        var newlist = new Mal.List.empty();
        newlist.vs.append(first);
        for (var iter = rest.iter(); iter.nonempty(); iter.step())
            newlist.vs.append(iter.deref());
        return newlist;
    }

    private static Mal.Val Concat(Mal.Val[] args, string name) throws Mal.Error {
        var newlist = new GLib.List<Mal.Val>();
        foreach (var listval in args) {
            if (listval is Mal.Nil)
                continue;
            var list = listval as Mal.Listlike;
            if (list == null)
                throw new Mal.Error.BAD_PARAMS("%s: expected a list", name);
            for (var iter = list.iter(); iter.nonempty(); iter.step())
                newlist.append(iter.deref());
        }
        return new Mal.List(newlist);
    }

    private static Mal.Val Vec(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        var a0 = args[0];
        var a0lst = a0 as Mal.List;
        if (a0lst != null) {
            var result = new Mal.Vector.with_size(a0lst.vs.length());
            uint i = 0;
            foreach (var x in a0lst.vs)
                result[i++] = x;
            return result;
        }
        if (a0 is Mal.Vector)
            return a0;
        throw new Mal.Error.BAD_PARAMS(
            "%s: expected a list or a vector", name);
    }

    private static Mal.Val Nth(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(2, args, name);
        var list = args[0] as Mal.Listlike;
        var index = args[1] as Mal.Num;
        if (list == null || index == null)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a list and a number", name);
        if (index.v < 0)
            throw new Mal.Error.BAD_PARAMS(
                "%s: negative list index", name);
        Mal.Val? result = null;
        var vec = list as Mal.Vector;
        if (vec != null) {
            if (index.v < vec.length)
                result = vec[(uint)index.v];
        } else {
            var iter = list.iter();
            var i = index.v;
            while (!iter.empty()) {
                if (i == 0) {
                    result = iter.deref();
                    break;
                }
                iter.step();
                i--;
            }
        }
        if (result == null)
            throw new Mal.Error.BAD_PARAMS(
                "%s: list index out of range", name);
        return result;
    }

    private static Mal.Val First(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        var list = args[0] as Mal.Listlike;
        if (list == null)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a list number", name);
        Mal.Val? result = list.iter().deref();
        if (result == null)
            result = new Mal.Nil();
        return result;
    }

    private static Mal.Val Rest(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        var list = args[0] as Mal.Listlike;
        if (list == null)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a list", name);
        var result = new Mal.List.empty();
        for (var iter = list.iter().step(); iter.nonempty(); iter.step())
            result.vs.append(iter.deref());
        return result;
    }

    // Only manipulated by the two following functions.
    private static Mal.Val curr_exception = null;

    public static Mal.Val thrown_value(Mal.Error err) {
        if (err is Mal.Error.EXCEPTION_THROWN) {
            assert(curr_exception != null);
            Mal.Val toret = curr_exception;
            curr_exception = null;
            return toret;
        } else {
            return new Mal.String(err.message);
        }
    }

    private static Mal.Val Throw(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        assert(curr_exception == null);
        curr_exception = args[0];
        throw new Mal.Error.EXCEPTION_THROWN("core function throw called");
    }

    private static Mal.Val Apply(Mal.Val[] args, string name) throws Mal.Error {
        if (args.length < 2)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected at least two arguments", name);
        var function = args[0];
        uint len;
        Mal.Iterator it;
        var list = args[args.length - 1] as Mal.List;
        var vec = args[args.length - 1] as Mal.Vector;
        if (list != null) {
            len = list.vs.length();
            it = list.iter();
        }
        else if (vec != null) {
            len = vec.length;
            it = vec.iter();
        }
        else
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected final argument to be a list", name);
        var fnargs = new Mal.Val[args.length - 2 + len];
        uint i = 0;
        for (var j = 1; j < args.length - 1; ++j)
            fnargs[i++] = args[j];
        for (; it.nonempty(); it.step())
            fnargs[i++] = it.deref();
        return call_function(function, fnargs, name);
    }

    private static Mal.Val Map(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(2, args, name);
        var function = args[0];
        var list = args[1] as Mal.Listlike;
        if (list == null)
            throw new Mal.Error.BAD_PARAMS("%s: expected a list", name);
        var result = new Mal.List.empty();
        for (var iter = list.iter(); iter.nonempty(); iter.step()) {
            Mal.Val fnargs[1] = { iter.deref() };
            result.vs.append(call_function(function, fnargs, name));
        }
        return result;
    }

    private static Mal.Val Symbol(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        var s = args[0] as Mal.String;
        if (s == null)
            throw new Mal.Error.BAD_PARAMS("%s: expected a string", name);
        return new Mal.Sym(s.v);
    }

    private static Mal.Val FnKeyword(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        if (args[0] is Mal.Keyword)
            return args[0];
        var arg1 = args[0] as Mal.String;
        if (arg1 == null)
            throw new Mal.Error.BAD_PARAMS("%s: expected one string", name);
        return new Mal.Keyword(arg1.v);
    }

    private static Mal.Val Assoc(Mal.Val[] args, string name) throws Mal.Error {
        if (args.length % 2 == 0)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected an even number of arguments", name);

        var map = new Mal.Hashmap();
        var oldmap = args[0] as Mal.Hashmap;
        if (oldmap != null)
            foreach (var key in oldmap.vs.get_keys())
                map.insert(key, oldmap.vs[key]);
        else if (!(args[0] is Mal.Nil))
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a hash-map to modify", name);

        for (var i = 1; i < args.length; i += 2) {
            var key = args[i];
            var value = args[i+1];
            map.insert(key, value);
        }
        return map;
    }

    private static Mal.Val Dissoc(Mal.Val[] args, string name) throws Mal.Error {
        if (args.length == 0)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a hash-map to modify", name);

        var map = new Mal.Hashmap();
        var oldmap = args[0] as Mal.Hashmap;
        if (oldmap != null)
            foreach (var key in oldmap.vs.get_keys())
                map.insert(key, oldmap.vs[key]);
        else if (!(args[0] is Mal.Nil))
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a hash-map to modify", name);

        for (var i = 1; i < args.length; ++i) {
            var key = args[i];
            map.remove(key);
        }
        return map;
    }

// Can't call it BuiltinFunctionGet, or else valac defines
// BUILTIN_FUNCTION_GET_CLASS at the C level for this class, but that
// was already defined as the 'get class' macro for BuiltinFunction
// itself!
    private static Mal.Val GetFn(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(2, args, name);
        if (args[0] is Mal.Nil)
            return new Mal.Nil();
        var map = args[0] as Mal.Hashmap;
        if (map == null)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a hash-map to query", name);
        var key = args[1] as Mal.Hashable;
        if (key == null)
            throw new Mal.Error.HASH_KEY_TYPE_ERROR(
                "%s: bad type as hash key", name);
        var value = map.vs[key];
        return value != null ? value : new Mal.Nil();
    }

    private static Mal.Val Contains(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(2, args, name);
        if (args[0] is Mal.Nil)
            return new Mal.Bool(false);
        var map = args[0] as Mal.Hashmap;
        if (map == null)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a hash-map to query", name);
        var key = args[1] as Mal.Hashable;
        if (key == null)
            throw new Mal.Error.HASH_KEY_TYPE_ERROR(
                "%s: bad type as hash key", name);
        var value = map.vs[key];
        return new Mal.Bool(value != null);
    }

    private static Mal.Val Keys(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        var keys = new Mal.List.empty();
        if (args[0] is Mal.Nil)
            return keys;
        var map = args[0] as Mal.Hashmap;
        if (map == null)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a hash-map to query", name);
        foreach (var key in map.vs.get_keys())
            keys.vs.append(key);
        return keys;
    }

    private static Mal.Val Vals(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        var vals = new Mal.List.empty();
        if (args[0] is Mal.Nil)
            return vals;
        var map = args[0] as Mal.Hashmap;
        if (map == null)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a hash-map to query", name);
        foreach (var key in map.vs.get_keys())
            vals.vs.append(map.vs[key]);
        return vals;
    }

    private static Mal.Val FnReadline(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        string prompt = "";
        var arg1 = args[0] as Mal.String;
        if (arg1 != null)
            prompt = arg1.v;
        else if (!(arg1 is Mal.Nil))
          throw new Mal.Error.BAD_PARAMS(
                "%s: expected a string prompt", name);
        string? line = Readline.readline(prompt);
        if (line == null)
            return new Mal.Nil();
        return new Mal.String(line);
    }

    private static Mal.Val Meta(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        var vwm = args[0] as Mal.ValWithMetadata;
        if (vwm == null || vwm.metadata == null)
            return new Mal.Nil();
        return vwm.metadata;
    }

    private static Mal.Val Withmeta(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(2, args, name);
        var vwm = args[0] as Mal.ValWithMetadata;
        if (vwm == null)
            throw new Mal.Error.BAD_PARAMS(
                "%s: bad type for with-meta", name);
        var copied = vwm.copy();
        copied.metadata = args[1];
        return copied;
    }

    private static Mal.Val Timems(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(0, args, name);
        return new Mal.Num(GLib.get_real_time() / 1000);
    }

    private static Mal.Val Conj(Mal.Val[] args, string name) throws Mal.Error {
        if (args.length == 0)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a collection to modify", name);
        var oldvec = args[0] as Mal.Vector;
        if (oldvec != null) {
            var n = args.length - 1;
            var newvec = new Mal.Vector.with_size(oldvec.length + n);
            int i;
            for (i = 0; i < oldvec.length; i++)
                newvec[i] = oldvec[i];
            for (var j = 1; j < args.length; ++j)
                newvec[i++] = args[j];
            return newvec;
        }
        var oldlist = args[0] as Mal.List;
        if (oldlist != null) {
            var newlist = new Mal.List.empty();
            newlist.vs = oldlist.vs.copy();
            for (uint j = 1; j < args.length; ++j)
                newlist.vs.prepend(args[j]);
            return newlist;
        }
        throw new Mal.Error.BAD_PARAMS(
            "%s: expected a collection to modify", name);
    }

    private static Mal.Val Seq(Mal.Val[] args, string name) throws Mal.Error {
        BuiltinFunction.check_arg_count(1, args, name);
        Mal.List toret = args[0] as Mal.List;
        if (toret == null) {
            toret = new Mal.List.empty();
            var s = args[0] as Mal.String;
            if (s != null) {
                var str = s.v;
                if (str.length != 0) {
                    unowned string tail = str;
                    while (tail != "") {
                        unowned string new_tail = tail.next_char();
                        var ch = str.substring(str.length - tail.length,
                                               tail.length - new_tail.length);
                        toret.vs.append(new Mal.String(ch));
                        tail = new_tail;
                    }
                }
            } else {
            var collection = args[0] as Mal.Listlike;
            if (collection != null) {
                for (var iter = collection.iter(); iter.nonempty(); iter.step())
                    toret.vs.append(iter.deref());
            } else {
                throw new Mal.Error.BAD_PARAMS("%s: bad input type", name);
            }
            }
        }
        if (toret.vs.length() == 0)
            return new Mal.Nil();
        return toret;
    }

    private static void add_builtin(Mal.Env env,
                                    Mal.BuiltinFunction.CallFunc f,
                                    string name) {
        env.set(name, new BuiltinFunction(f, name));
    }

    public static void make_ns(Mal.Env env) {
        add_builtin(env, Add, "+");
        add_builtin(env, Sub, "-");
        add_builtin(env, Mul, "*");
        add_builtin(env, Div, "/");
        add_builtin(env, PrStr, "pr-str");
        add_builtin(env, Str, "str");
        add_builtin(env, Prn, "prn");
        add_builtin(env, Println, "println");
        add_builtin(env, ReadString, "read-string");
        add_builtin(env, Slurp, "slurp");
        add_builtin(env, FnList, "list");
        add_builtin(env, ListP, "list?");
        add_builtin(env, NilP, "nil?");
        add_builtin(env, TrueP, "true?");
        add_builtin(env, FalseP, "false?");
        add_builtin(env, NumberP, "number?");
        add_builtin(env, StringP, "string?");
        add_builtin(env, Symbol, "symbol");
        add_builtin(env, SymbolP, "symbol?");
        add_builtin(env, FnKeyword, "keyword");
        add_builtin(env, KeywordP, "keyword?");
        add_builtin(env, FnVector, "vector");
        add_builtin(env, VectorP, "vector?");
        add_builtin(env, SequentialP, "sequential?");
        add_builtin(env, HashMap, "hash-map");
        add_builtin(env, MapP, "map?");
        add_builtin(env, EmptyP, "empty?");
        add_builtin(env, FnP, "fn?");
        add_builtin(env, MacroP, "macro?");
        add_builtin(env, Count, "count");
        add_builtin(env, EQ, "=");
        add_builtin(env, LT, "<");
        add_builtin(env, LE, "<=");
        add_builtin(env, GT, ">");
        add_builtin(env, GE, ">=");
        add_builtin(env, FnAtom, "atom");
        add_builtin(env, AtomP, "atom?");
        add_builtin(env, Deref, "deref");
        add_builtin(env, Reset, "reset!");
        add_builtin(env, Swap, "swap!");
        add_builtin(env, Cons, "cons");
        add_builtin(env, Concat, "concat");
        add_builtin(env, Vec, "vec");
        add_builtin(env, Nth, "nth");
        add_builtin(env, First, "first");
        add_builtin(env, Rest, "rest");
        add_builtin(env, Throw, "throw");
        add_builtin(env, Apply, "apply");
        add_builtin(env, Map, "map");
        add_builtin(env, Assoc, "assoc");
        add_builtin(env, Dissoc, "dissoc");
        add_builtin(env, GetFn, "get");
        add_builtin(env, Contains, "contains?");
        add_builtin(env, Keys, "keys");
        add_builtin(env, Vals, "vals");
        add_builtin(env, FnReadline, "readline");
        add_builtin(env, Meta, "meta");
        add_builtin(env, Withmeta, "with-meta");
        add_builtin(env, Conj, "conj");
        add_builtin(env, Timems, "time-ms");
        add_builtin(env, Seq, "seq");
    }
}
