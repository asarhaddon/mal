class Mal.Env : GC.Object {
    private GLib.HashTable<weak Mal.Sym, weak Mal.Val> data;
    weak Mal.Env? outer;

    construct {
        data = new GLib.HashTable<weak Mal.Sym, weak Mal.Val>(
            Mal.Hashable.hash, Mal.Hashable.equal);
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
        foreach (var key in data.get_keys()) {
            key.visit();
            data[key].visit();
        }
    }

    public Env.funcall(Mal.Env outer_, Mal.Listlike binds, Mal.List exprs)
    throws Mal.Error {
        outer = outer_;
        var binditer = binds.iter();
        unowned var exprlist = exprs.vs;

        while (binditer.nonempty()) {
            var paramsym = binditer.deref() as Mal.Sym;
            if (paramsym.v == "&") {
                binditer.step();
                var rest = binditer.deref();
                binditer.step();
                if (rest == null || binditer.nonempty())
                    throw new Mal.Error.BAD_PARAMS(
                        "expected exactly one parameter name after &");
                var rest_expr = new Mal.List.empty();
                rest_expr.vs = exprlist.copy();
                set(rest as Mal.Sym, rest_expr);
                return;
            } else {
                if (exprlist == null)
                    throw new Mal.Error.BAD_PARAMS(
                        "too few arguments for function");
                set(paramsym, exprlist.data);
                binditer.step();
                exprlist = exprlist.next;
            }
        }
        if (exprlist != null)
            throw new Mal.Error.BAD_PARAMS("too many arguments for function");
    }

    // Use the 'new' keyword to silence warnings about 'set' and 'get'
    // already having meanings that we're overwriting
    public new void set(Mal.Sym key, Mal.Val f) {
        data[key] = f;
    }

    public new Mal.Val? get(Mal.Sym key) {
        if (key in data)
            return data[key];
        if (outer == null)
            return null;
        return outer.get(key);
    }
}
