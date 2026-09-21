namespace Mal {
    string pr_str(Mal.Val val, bool print_readably = true) {
        if (val is Mal.Nil)
            return "nil";
        var b = val as Mal.Bool;
        if (b != null)
            return b.v ? "true" : "false";
        var y = val as Mal.Sym;
        if (y != null)
            return y.v;
        var k = val as Mal.Keyword;
        if (k != null)
            return ":" + k.v;
        var n = val as Mal.Num;
        if (n != null)
            return ("%"+int64.FORMAT_MODIFIER+"d")
                .printf(n.v);
        var t = val as Mal.String;
        if (t != null) {
            string s = t.v;
            if (print_readably)
                s = "\"%s\"".printf(s.replace("\\", "\\\\")
                                    .replace("\n", "\\n").
                                    replace("\"", "\\\""));
            return s;
        }
        var l = val as Mal.List;
        if (l != null) {
            return "(" + pr_listlike(l, print_readably, " ") + ")";
        }
        var v = val as Mal.Vector;
        if (v != null) {
            return "[" + pr_listlike(v, print_readably, " ") + "]";
        }
        var m = val as Mal.Hashmap;
        if (m != null) {
            string toret = "{";
            string sep = "";
            var map = m.vs;
            foreach (var key in map.get_keys()) {
                toret += (sep + pr_str(key, print_readably) + " " +
                          pr_str(map[key], print_readably));
                sep = " ";
            }
            toret += "}";
            return toret;
        }
        var bf = val as Mal.BuiltinFunction;
        if (bf != null) {
            return "#<builtin:%s>".printf(bf.name());
        }
        var mf = val as Mal.Function;
        if (mf != null) {
            if (mf.is_macro)
                return "#<macro>";
            return "#<function>";
        }
        var a = val as Mal.Atom;
        assert(a != null);
        return "(atom %s)".printf(pr_str(a.v, print_readably));
    }

    string pr_listlike(Listlike xs, bool print_readably, string separator) {
        string result = "";
        for (var iter = xs.iter(); iter.nonempty(); iter.step()) {
            if (0 != result.length)
                result += separator;
            result += pr_str(iter.deref(), print_readably);
        }
        return result;
    }
    string pr_list(Val[] xs, bool print_readably, string separator) {
        string result = "";
        foreach (var x in xs) {
            if (0 != result.length)
                result += separator;
            result += pr_str(x, print_readably);
        }
        return result;
    }
}
