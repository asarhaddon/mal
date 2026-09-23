class Mal.Env : GC.Object {
    private GLib.HashTable<string, weak Mal.Val> data;
    private weak Mal.Env? outer;

    construct {
        data = new GLib.HashTable<string, weak Mal.Val>(
            str_hash, str_equal);
    }

    public Env.within(Mal.Env outer_) {
        outer = outer_;
    }

    public Env() {
        outer = null;
    }

    public override void gc_traverse() {
        base.gc_traverse();
        if (outer != null)
            outer.visit();
        foreach (var v in data.get_values())
            v.visit();
    }

    public Env.funcall(Mal.Env outer_, string[] binds, Mal.Val[] exprs)
    throws Mal.Error {
        outer = outer_;

        if (2 <= binds.length && binds[binds.length - 2] == "&") {
            if (exprs.length < binds.length - 2)
                throw new Mal.Error.BAD_PARAMS(
                    "fn* function call: expected at least %u arguments, got: %s",
                    binds.length - 2, pr_list(exprs, true, " "));
            for (uint i = 0; i < binds.length - 2; ++i)
                set(binds[i], exprs[i]);
            var rest_expr = new Mal.List.empty();
            for (uint i = binds.length - 2; i < exprs.length; ++i)
                rest_expr.vs.append(exprs[i]);
            set(binds[binds.length - 1], rest_expr);
        }
        else {
            if (exprs.length != binds.length)
                throw new Mal.Error.BAD_PARAMS(
                    "fn* function call: expected %u argument(s), got: %s",
                    binds.length, pr_list(exprs, true, " "));
            for (uint i = 0; i < binds.length; ++i)
                set(binds[i], exprs[i]);
        }
    }

    // Use the 'new' keyword to silence warnings about 'set' and 'get'
    // already having meanings that we're overwriting
    public new void set(string key, Mal.Val f) {
        data[key] = f;
    }

    public new Mal.Val? get(string key) {
        if (key in data)
            return data[key];
        if (outer == null)
            return null;
        return outer.get(key);
    }
}
