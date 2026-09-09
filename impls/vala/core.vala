abstract class Mal.BuiltinFunctionDyadicArithmetic : Mal.BuiltinFunction {
    public abstract int64 result(int64 a, int64 b);
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(2, args);
        Mal.Num a = args.vs.data as Mal.Num;
        Mal.Num b = args.vs.next.data as Mal.Num;
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

class Mal.BuiltinFunctionPrStr : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionPrStr();
    }
    public override string name() { return "pr-str"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        string result = pr_list(args, true, " ");
        return new Mal.String(result);
    }
}

class Mal.BuiltinFunctionStr : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionStr();
    }
    public override string name() { return "str"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        string result = pr_list(args, false, "");
        return new Mal.String(result);
    }
}

class Mal.BuiltinFunctionPrn : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionPrn();
    }
    public override string name() { return "prn"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        stdout.printf(pr_list(args, true, " "));
        stdout.printf("\n");
        return new Mal.Nil();
    }
}

class Mal.BuiltinFunctionPrintln : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionPrintln();
    }
    public override string name() { return "println"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        stdout.printf(pr_list(args, false, " "));
        stdout.printf("\n");
        return new Mal.Nil();
    }
}

class Mal.BuiltinFunctionReadString : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionReadString();
    }
    public override string name() { return "read-string"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        var arg1 = args.vs.data as Mal.String;
        if (arg1 == null)
            throw new Mal.Error.BAD_PARAMS("%s: expected one string", name());
        return Reader.read_str(arg1.v);
    }
}

class Mal.BuiltinFunctionSlurp : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionSlurp();
    }
    public override string name() { return "slurp"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        var arg1 = args.vs.data as Mal.String;
        if (arg1 == null)
            throw new Mal.Error.BAD_PARAMS("%s: expected one string", name());
        string filename = arg1.v;
        string contents;
        try {
            FileUtils.get_contents(filename, out contents);
        } catch (FileError e) {
            throw new Mal.Error.BAD_PARAMS("%s: unable to read '%s': %s",
                                           name(), filename, e.message);
        }
        return new Mal.String(contents);
    }
}

class Mal.BuiltinFunctionList : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionList();
    }
    public override string name() { return "list"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        return args;
    }
}

class Mal.BuiltinFunctionListP : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionListP();
    }
    public override string name() { return "list?"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        return new Mal.Bool(args.vs.data is Mal.List);
    }
}

class Mal.BuiltinFunctionSequentialP : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionSequentialP();
    }
    public override string name() { return "sequential?"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        return new Mal.Bool(args.vs.data is Mal.List ||
                            args.vs.data is Mal.Vector);
    }
}

class Mal.BuiltinFunctionNilP : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionNilP();
    }
    public override string name() { return "nil?"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        return new Mal.Bool(args.vs.data is Mal.Nil);
    }
}

class Mal.BuiltinFunctionTrueP : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionTrueP();
    }
    public override string name() { return "true?"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        var arg1 = args.vs.data as Mal.Bool;
        return new Mal.Bool(arg1 != null && arg1.v);
    }
}

class Mal.BuiltinFunctionFalseP : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionFalseP();
    }
    public override string name() { return "false?"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        var arg1 = args.vs.data as Mal.Bool;
        return new Mal.Bool(arg1 != null && !arg1.v);
    }
}

class Mal.BuiltinFunctionNumberP : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionNumberP();
    }
    public override string name() { return "number?"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        return new Mal.Bool(args.vs.data is Mal.Num);
    }
}

class Mal.BuiltinFunctionStringP : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionStringP();
    }
    public override string name() { return "string?"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        return new Mal.Bool(args.vs.data is Mal.String);
    }
}

class Mal.BuiltinFunctionSymbolP : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionSymbolP();
    }
    public override string name() { return "symbol?"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        return new Mal.Bool(args.vs.data is Mal.Sym);
    }
}

class Mal.BuiltinFunctionKeywordP : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionKeywordP();
    }
    public override string name() { return "keyword?"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        return new Mal.Bool(args.vs.data is Mal.Keyword);
    }
}

class Mal.BuiltinFunctionVector : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionVector();
    }
    public override string name() { return "vector"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        var result = new Mal.Vector.with_size(args.vs.length());
        uint i = 0;
        foreach (var value in args.vs)
            result[i++] = value;
        return result;
    }
}

class Mal.BuiltinFunctionVectorP : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionVectorP();
    }
    public override string name() { return "vector?"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        return new Mal.Bool(args.vs.data is Mal.Vector);
    }
}

class Mal.BuiltinFunctionHashMap : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionHashMap();
    }
    public override string name() { return "hash-map"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        var map = new Mal.Hashmap();
        for (var iter = args.iter(); iter.nonempty(); iter.step()) {
            var key = iter.deref();
            var value = iter.step().deref();
            if (value == null)
                throw new Mal.Error.BAD_PARAMS(
                    "%s: expected an even number of arguments", name());
            map.insert(key, value);
        }
        return map;
    }
}

class Mal.BuiltinFunctionMapP : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionMapP();
    }
    public override string name() { return "map?"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        return new Mal.Bool(args.vs.data is Mal.Hashmap);
    }
}

class Mal.BuiltinFunctionEmptyP : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionEmptyP();
    }
    public override string name() { return "empty?"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        var list = args.vs.data as Mal.Listlike;
        if (list == null)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a list-like argument", name());
        return new Mal.Bool(list.iter().deref() == null);
    }
}

class Mal.BuiltinFunctionFnP : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionFnP();
    }
    public override string name() { return "fn?"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        if (args.vs.data is Mal.BuiltinFunction)
            return new Mal.Bool(true);
        var fn = args.vs.data as Mal.Function;
        return new Mal.Bool(fn != null && !fn.is_macro);
    }
}

class Mal.BuiltinFunctionMacroP : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionMacroP();
    }
    public override string name() { return "macro?"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        var fn = args.vs.data as Mal.Function;
        return new Mal.Bool(fn != null && fn.is_macro);
    }
}

class Mal.BuiltinFunctionCount : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionCount();
    }
    public override string name() { return "count"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        if (args.vs.data is Mal.Nil)
            return new Mal.Num(0);     // nil is treated like ()
        var l = args.vs.data as Mal.List;
        if (l != null)
            return new Mal.Num(l.vs.length());
        var v = args.vs.data as Mal.Vector;
        if (v != null)
            return new Mal.Num(v.length);
        throw new Mal.Error.BAD_PARAMS(
            "%s: expected a list argument", name());
    }
}

class Mal.BuiltinFunctionEQ : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionEQ();
    }
    public override string name() { return "="; }
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
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(2, args);
        return new Mal.Bool(eq(args.vs.data, args.vs.next.data));
    }
}

abstract class Mal.BuiltinFunctionNumberCmp : Mal.BuiltinFunction {
    public abstract bool result(int64 a, int64 b);
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(2, args);
        Mal.Num a = args.vs.data as Mal.Num;
        Mal.Num b = args.vs.next.data as Mal.Num;
        if (a == null || b == null)
            throw new Mal.Error.BAD_PARAMS("%s: expected two numbers", name());
        return new Mal.Bool(result(a.v, b.v));
    }
}

class Mal.BuiltinFunctionLT : Mal.BuiltinFunctionNumberCmp {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionLT();
    }
    public override string name() { return "<"; }
    public override bool result(int64 a, int64 b) { return a<b; }
}

class Mal.BuiltinFunctionLE : Mal.BuiltinFunctionNumberCmp {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionLE();
    }
    public override string name() { return "<="; }
    public override bool result(int64 a, int64 b) { return a<=b; }
}

class Mal.BuiltinFunctionGT : Mal.BuiltinFunctionNumberCmp {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionGT();
    }
    public override string name() { return ">"; }
    public override bool result(int64 a, int64 b) { return a>b; }
}

class Mal.BuiltinFunctionGE : Mal.BuiltinFunctionNumberCmp {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionGE();
    }
    public override string name() { return ">="; }
    public override bool result(int64 a, int64 b) { return a>=b; }
}

class Mal.BuiltinFunctionAtom : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionAtom();
    }
    public override string name() { return "atom"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        return new Mal.Atom(args.vs.data);
    }
}

class Mal.BuiltinFunctionAtomP : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionAtomP();
    }
    public override string name() { return "atom?"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        return new Mal.Bool(args.vs.data is Mal.Atom);
    }
}

class Mal.BuiltinFunctionDeref : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionDeref();
    }
    public override string name() { return "deref"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        var atom = args.vs.data as Mal.Atom;
        if (atom == null)
            throw new Mal.Error.BAD_PARAMS("%s: expected an atom", name());
        return atom.v;
    }
}

class Mal.BuiltinFunctionReset : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionReset();
    }
    public override string name() { return "reset!"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(2, args);
        var atom = args.vs.data as Mal.Atom;
        if (atom == null)
            throw new Mal.Error.BAD_PARAMS("%s: expected an atom", name());
        atom.v = args.vs.next.data;
        return atom.v;
    }
}

Mal.Val call_function(Mal.Val function, GLib.List<Mal.Val> args, string caller)
throws Mal.Error {
    var fnargs = new Mal.List(args);
    var bf = function as Mal.BuiltinFunction;
    if (bf != null)
        return bf.call(fnargs);
    var fn = function as Mal.Function;
    if (fn != null) {
        var env = new Mal.Env.funcall(fn.env, fn.parameters, fnargs);
        return Mal.Main.EVAL(fn.body, env);
    } else {
        throw new Mal.Error.CANNOT_APPLY("%s: expected a function", caller);
    }
}

class Mal.BuiltinFunctionSwap : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionSwap();
    }
    public override string name() { return "swap!"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        if (args.vs.length() < 2)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected at least two arguments", name());
        var atom = args.vs.data as Mal.Atom;
        if (atom == null)
            throw new Mal.Error.BAD_PARAMS("%s: expected an atom", name());
        var function = args.vs.next.data;
        var fnargs = args.vs.next.next.copy();
        fnargs.prepend(atom.v);
        atom.v = call_function(function, fnargs, name());
        return atom.v;
    }
}

class Mal.BuiltinFunctionCons : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionCons();
    }
    public override string name() { return "cons"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(2, args);
        var first = args.vs.data;
        var rest = args.vs.next.data as Mal.Listlike;
        if (rest == null) {
            throw new Mal.Error.BAD_PARAMS("%s: expected a list", name());
        }
        var newlist = new Mal.List.empty();
        newlist.vs.append(first);
        for (var iter = rest.iter(); iter.nonempty(); iter.step())
            newlist.vs.append(iter.deref());
        return newlist;
    }
}

class Mal.BuiltinFunctionConcat : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionConcat();
    }
    public override string name() { return "concat"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        var newlist = new GLib.List<Mal.Val>();
        foreach (var listval in args.vs) {
            if (listval is Mal.Nil)
                continue;
            var list = listval as Mal.Listlike;
            if (list == null)
                throw new Mal.Error.BAD_PARAMS("%s: expected a list", name());
            for (var iter = list.iter(); iter.nonempty(); iter.step())
                newlist.append(iter.deref());
        }
        return new Mal.List(newlist);
    }
}

class Mal.BuiltinFunctionVec : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionVec();
    }
    public override string name() { return "vec"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        var a0 = args.vs.data;
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
            "%s: expected a list or a vector", name());
    }
}

class Mal.BuiltinFunctionNth : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionNth();
    }
    public override string name() { return "nth"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(2, args);
        var list = args.vs.data as Mal.Listlike;
        var index = args.vs.next.data as Mal.Num;
        if (list == null || index == null)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a list and a number", name());
        if (index.v < 0)
            throw new Mal.Error.BAD_PARAMS(
                "%s: negative list index", name());
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
                "%s: list index out of range", name());
        return result;
    }
}

class Mal.BuiltinFunctionFirst : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionFirst();
    }
    public override string name() { return "first"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        var list = args.vs.data as Mal.Listlike;
        if (list == null)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a list number", name());
        Mal.Val? result = list.iter().deref();
        if (result == null)
            result = new Mal.Nil();
        return result;
    }
}

class Mal.BuiltinFunctionRest : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionRest();
    }
    public override string name() { return "rest"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        var list = args.vs.data as Mal.Listlike;
        if (list == null)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a list", name());
        var result = new Mal.List.empty();
        for (var iter = list.iter().step(); iter.nonempty(); iter.step())
            result.vs.append(iter.deref());
        return result;
    }
}

class Mal.BuiltinFunctionThrow : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionThrow();
    }
    private static weak Mal.Val? curr_exception;
    static construct {
        curr_exception = null;
    }
    public static void clear() {
        curr_exception = null;
    }
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

    public override string name() { return "throw"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        assert(curr_exception == null);
        curr_exception = args.vs.data;
        throw new Mal.Error.EXCEPTION_THROWN("core function throw called");
    }
    public override void gc_traverse() {
        base.gc_traverse();
        if (curr_exception != null)
            curr_exception.visit();
    }
}

class Mal.BuiltinFunctionApply : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionApply();
    }
    public override string name() { return "apply"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        if (args.vs.length() < 2)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected at least two arguments", name());
        var function = args.vs.data;
        unowned GLib.List<Mal.Val> lastlink = args.vs.last();
        var list = lastlink.data as Mal.Listlike;
        if (list == null)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected final argument to be a list", name());
        var fnargs = new GLib.List<Mal.Val>();
        for (var iter = list.iter(); iter.nonempty(); iter.step())
            fnargs.append(iter.deref());
        for (unowned GLib.List<Mal.Val> link = lastlink.prev;
             link != args.vs; link = link.prev)
            fnargs.prepend(link.data);
        return call_function(function, fnargs, name());
    }
}

class Mal.BuiltinFunctionMap : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionMap();
    }
    public override string name() { return "map"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(2, args);
        var function = args.vs.data;
        var list = args.vs.next.data as Mal.Listlike;
        if (list == null)
            throw new Mal.Error.BAD_PARAMS("%s: expected a list", name());
        var result = new Mal.List.empty();
        for (var iter = list.iter(); iter.nonempty(); iter.step()) {
            var fnargs = new GLib.List<Mal.Val>();
            fnargs.append(iter.deref());
            result.vs.append(call_function(function, fnargs, name()));
        }
        return result;
    }
}

class Mal.BuiltinFunctionSymbol : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionSymbol();
    }
    public override string name() { return "symbol"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        var s = args.vs.data as Mal.String;
        if (s == null)
            throw new Mal.Error.BAD_PARAMS("%s: expected a string", name());
        return new Mal.Sym(s.v);
    }
}

class Mal.BuiltinFunctionKeyword : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionKeyword();
    }
    public override string name() { return "keyword"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        if (args.vs.data is Mal.Keyword)
            return args.vs.data;
        var arg1 = args.vs.data as Mal.String;
        if (arg1 == null)
            throw new Mal.Error.BAD_PARAMS("%s: expected one string", name());
        return new Mal.Keyword(arg1.v);
    }
}

class Mal.BuiltinFunctionAssoc : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionAssoc();
    }
    public override string name() { return "assoc"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        var iter = args.iter();
        var oldmap = iter.deref() as Mal.Hashmap;
        if (iter.deref() is Mal.Nil)
            oldmap = new Mal.Hashmap();
        if (oldmap == null)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a hash-map to modify", name());

        var map = new Mal.Hashmap();
        foreach (var key in oldmap.vs.get_keys())
            map.insert(key, oldmap.vs[key]);

        for (iter.step(); iter.nonempty(); iter.step()) {
            var key = iter.deref();
            var value = iter.step().deref();
            if (value == null)
                throw new Mal.Error.BAD_PARAMS(
                    "%s: expected an even number of arguments", name());
            map.insert(key, value);
        }
        return map;
    }
}

class Mal.BuiltinFunctionDissoc : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionDissoc();
    }
    public override string name() { return "dissoc"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        if (args.vs.length() == 0)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a hash-map to modify", name());
        var iter = args.iter();
        var oldmap = iter.deref() as Mal.Hashmap;
        if (iter.deref() is Mal.Nil)
            oldmap = new Mal.Hashmap();
        if (oldmap == null)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a hash-map to modify", name());

        var map = new Mal.Hashmap();
        foreach (var key in oldmap.vs.get_keys())
            map.insert(key, oldmap.vs[key]);

        for (iter.step(); iter.nonempty(); iter.step()) {
            var key = iter.deref();
            map.remove(key);
        }
        return map;
    }
}

// Can't call it BuiltinFunctionGet, or else valac defines
// BUILTIN_FUNCTION_GET_CLASS at the C level for this class, but that
// was already defined as the 'get class' macro for BuiltinFunction
// itself!
class Mal.BuiltinFunctionGetFn : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionGetFn();
    }
    public override string name() { return "get"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(2, args);
        if (args.vs.data is Mal.Nil)
            return new Mal.Nil();
        var map = args.vs.data as Mal.Hashmap;
        if (map == null)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a hash-map to query", name());
        var key = args.vs.next.data as Mal.Hashable;
        if (key == null)
            throw new Mal.Error.HASH_KEY_TYPE_ERROR(
                "%s: bad type as hash key", name());
        var value = map.vs[key];
        return value != null ? value : new Mal.Nil();
    }
}

class Mal.BuiltinFunctionContains : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionContains();
    }
    public override string name() { return "contains?"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(2, args);
        if (args.vs.data is Mal.Nil)
            return new Mal.Bool(false);
        var map = args.vs.data as Mal.Hashmap;
        if (map == null)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a hash-map to query", name());
        var key = args.vs.next.data as Mal.Hashable;
        if (key == null)
            throw new Mal.Error.HASH_KEY_TYPE_ERROR(
                "%s: bad type as hash key", name());
        var value = map.vs[key];
        return new Mal.Bool(value != null);
    }
}

class Mal.BuiltinFunctionKeys : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionKeys();
    }
    public override string name() { return "keys"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        var keys = new Mal.List.empty();
        if (args.vs.data is Mal.Nil)
            return keys;
        var map = args.vs.data as Mal.Hashmap;
        if (map == null)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a hash-map to query", name());
        foreach (var key in map.vs.get_keys())
            keys.vs.append(key);
        return keys;
    }
}

class Mal.BuiltinFunctionVals : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionVals();
    }
    public override string name() { return "vals"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        var vals = new Mal.List.empty();
        if (args.vs.data is Mal.Nil)
            return vals;
        var map = args.vs.data as Mal.Hashmap;
        if (map == null)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a hash-map to query", name());
        foreach (var key in map.vs.get_keys())
            vals.vs.append(map.vs[key]);
        return vals;
    }
}

class Mal.BuiltinFunctionReadline : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionReadline();
    }
    public override string name() { return "readline"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        string prompt = "";
        var arg1 = args.vs.data as Mal.String;
        if (arg1 != null)
            prompt = arg1.v;
        else if (!(arg1 is Mal.Nil))
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a string prompt", name());
        string? line = Readline.readline(prompt);
        if (line == null)
            return new Mal.Nil();
        return new Mal.String(line);
    }
}

class Mal.BuiltinFunctionMeta : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionMeta();
    }
    public override string name() { return "meta"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        var vwm = args.vs.data as Mal.ValWithMetadata;
        if (vwm == null || vwm.metadata == null)
            return new Mal.Nil();
        return vwm.metadata;
    }
}

class Mal.BuiltinFunctionWithMeta : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionWithMeta();
    }
    public override string name() { return "with-meta"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(2, args);
        var vwm = args.vs.data as Mal.ValWithMetadata;
        if (vwm == null)
            throw new Mal.Error.BAD_PARAMS(
                "%s: bad type for with-meta", name());
        var copied = vwm.copy();
        copied.metadata = args.vs.next.data;
        return copied;
    }
}

class Mal.BuiltinFunctionTimeMs : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionTimeMs();
    }
    public override string name() { return "time-ms"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(0, args);
        return new Mal.Num(GLib.get_real_time() / 1000);
    }
}

class Mal.BuiltinFunctionConj : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionConj();
    }
    public override string name() { return "conj"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        if (args.vs.length() == 0)
            throw new Mal.Error.BAD_PARAMS(
                "%s: expected a collection to modify", name());
        var oldvec = args.vs.data as Mal.Vector;
        if (oldvec != null) {
            var n = args.vs.length() - 1;
            var newvec = new Mal.Vector.with_size(oldvec.length + n);
            int i;
            for (i = 0; i < oldvec.length; i++)
                newvec[i] = oldvec[i];
            foreach (var x in args.vs.next)
                newvec[i++] = x;
            return newvec;
        }
        var oldlist = args.vs.data as Mal.List;
        if (oldlist != null) {
            var newlist = new Mal.List.empty();
            newlist.vs = oldlist.vs.copy();
            foreach (var x in args.vs.next)
                newlist.vs.prepend(x);
            return newlist;
        }
        throw new Mal.Error.BAD_PARAMS(
            "%s: expected a collection to modify", name());
    }
}

class Mal.BuiltinFunctionSeq : Mal.BuiltinFunction {
    public override Mal.ValWithMetadata copy() {
        return new Mal.BuiltinFunctionSeq();
    }
    public override string name() { return "seq"; }
    public override Mal.Val call(Mal.List args) throws Mal.Error {
        check_arg_count(1, args);
        Mal.List toret = args.vs.data as Mal.List;
        if (toret == null) {
            toret = new Mal.List.empty();
            var s = args.vs.data as Mal.String;
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
            var collection = args.vs.data as Mal.Listlike;
            if (collection != null) {
                for (var iter = collection.iter(); iter.nonempty(); iter.step())
                    toret.vs.append(iter.deref());
            } else {
                throw new Mal.Error.BAD_PARAMS("%s: bad input type", name());
            }
            }
        }
        if (toret.vs.length() == 0)
            return new Mal.Nil();
        return toret;
    }
}

class Mal.Core {

    // Avoid a global variable, that would artificially increase the
    // number of roots when debugging the garbage collector.

    private static void add_builtin(Mal.Env env, Mal.BuiltinFunction f) {
        env.set(new Mal.Sym(f.name()), f);
    }

    public static void make_ns(Mal.Env env) {
        add_builtin(env, new BuiltinFunctionAdd());
        add_builtin(env, new BuiltinFunctionSub());
        add_builtin(env, new BuiltinFunctionMul());
        add_builtin(env, new BuiltinFunctionDiv());
        add_builtin(env, new BuiltinFunctionPrStr());
        add_builtin(env, new BuiltinFunctionStr());
        add_builtin(env, new BuiltinFunctionPrn());
        add_builtin(env, new BuiltinFunctionPrintln());
        add_builtin(env, new BuiltinFunctionReadString());
        add_builtin(env, new BuiltinFunctionSlurp());
        add_builtin(env, new BuiltinFunctionList());
        add_builtin(env, new BuiltinFunctionListP());
        add_builtin(env, new BuiltinFunctionNilP());
        add_builtin(env, new BuiltinFunctionTrueP());
        add_builtin(env, new BuiltinFunctionFalseP());
        add_builtin(env, new BuiltinFunctionNumberP());
        add_builtin(env, new BuiltinFunctionStringP());
        add_builtin(env, new BuiltinFunctionSymbol());
        add_builtin(env, new BuiltinFunctionSymbolP());
        add_builtin(env, new BuiltinFunctionKeyword());
        add_builtin(env, new BuiltinFunctionKeywordP());
        add_builtin(env, new BuiltinFunctionVector());
        add_builtin(env, new BuiltinFunctionVectorP());
        add_builtin(env, new BuiltinFunctionSequentialP());
        add_builtin(env, new BuiltinFunctionHashMap());
        add_builtin(env, new BuiltinFunctionMapP());
        add_builtin(env, new BuiltinFunctionEmptyP());
        add_builtin(env, new BuiltinFunctionFnP());
        add_builtin(env, new BuiltinFunctionMacroP());
        add_builtin(env, new BuiltinFunctionCount());
        add_builtin(env, new BuiltinFunctionEQ());
        add_builtin(env, new BuiltinFunctionLT());
        add_builtin(env, new BuiltinFunctionLE());
        add_builtin(env, new BuiltinFunctionGT());
        add_builtin(env, new BuiltinFunctionGE());
        add_builtin(env, new BuiltinFunctionAtom());
        add_builtin(env, new BuiltinFunctionAtomP());
        add_builtin(env, new BuiltinFunctionDeref());
        add_builtin(env, new BuiltinFunctionReset());
        add_builtin(env, new BuiltinFunctionSwap());
        add_builtin(env, new BuiltinFunctionCons());
        add_builtin(env, new BuiltinFunctionConcat());
        add_builtin(env, new BuiltinFunctionVec());
        add_builtin(env, new BuiltinFunctionNth());
        add_builtin(env, new BuiltinFunctionFirst());
        add_builtin(env, new BuiltinFunctionRest());
        add_builtin(env, new BuiltinFunctionThrow());
        add_builtin(env, new BuiltinFunctionApply());
        add_builtin(env, new BuiltinFunctionMap());
        add_builtin(env, new BuiltinFunctionAssoc());
        add_builtin(env, new BuiltinFunctionDissoc());
        add_builtin(env, new BuiltinFunctionGetFn());
        add_builtin(env, new BuiltinFunctionContains());
        add_builtin(env, new BuiltinFunctionKeys());
        add_builtin(env, new BuiltinFunctionVals());
        add_builtin(env, new BuiltinFunctionReadline());
        add_builtin(env, new BuiltinFunctionMeta());
        add_builtin(env, new BuiltinFunctionWithMeta());
        add_builtin(env, new BuiltinFunctionTimeMs());
        add_builtin(env, new BuiltinFunctionConj());
        add_builtin(env, new BuiltinFunctionSeq());
    }
}
