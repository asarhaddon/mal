public errordomain Mal.Error {
    BAD_TOKEN,
    PARSE_ERROR,
    HASH_KEY_TYPE_ERROR,
    ENV_LOOKUP_FAILED,
    BAD_PARAMS,
    CANNOT_APPLY,
    EXCEPTION_THROWN,
}

abstract class Mal.Val : GC.Object {
    public virtual bool truth_value() { return true; }
}

abstract class Mal.Hashable : Mal.Val {
    public string hashkey;
    public static uint hash(Hashable h) { return str_hash(h.hashkey); }
    public static bool equal(Hashable hl, Hashable hr) {
        return hl.hashkey == hr.hashkey;
    }
}

class Mal.Bool : Mal.Hashable {
    public bool v;
    public Bool(bool value) {
        v = value;
        hashkey = value ? "bt" : "bf";
    }
    public override bool truth_value() { return v; }
}

// Mal.Listlike is a subclass of Mal.Val which includes both lists and
// vectors, and provides a common iterator API so that core functions
// and special forms can treat them the same.
//
// Most core functions that take a list argument also accept nil. To
// make that easy, Mal.Nil also derives from Mal.Listlike.
abstract class Mal.Listlike : Mal.ValWithMetadata {
    public abstract Mal.Iterator iter();
    public override void gc_traverse() {
        base.gc_traverse();
        for (var it = iter(); it.nonempty(); it.step())
            it.deref().visit();
    }
}

abstract class Mal.Iterator : GLib.Object {
    public abstract Mal.Val? deref();
    public abstract Mal.Iterator step();
    public bool empty() { return deref() == null; }
    public bool nonempty() { return deref() != null; }
}

// ValWithMetadata is a subclass of Mal.Val which includes every value
// type you can put metadata on. Value types implementing this class
// must provide a copy() method, because with-meta has to make a copy
// of the value with new metadata.
abstract class Mal.ValWithMetadata : Mal.Val {
    public weak Mal.Val? metadata;
    construct {
        metadata = null;
    }
    public abstract Mal.ValWithMetadata copy();
    public override void gc_traverse() {
        base.gc_traverse();
        if (metadata != null)
            metadata.visit();
    }
}

class Mal.Nil : Mal.Listlike {
    public override bool truth_value() { return false; }
    public override Mal.Iterator iter() { return new Mal.NilIterator(); }
    public override Mal.ValWithMetadata copy() { return new Mal.Nil(); }
}

class Mal.NilIterator : Mal.Iterator {
    public override Mal.Val? deref() { return null; }
    public override Mal.Iterator step() { return this; }
}

class Mal.List : Mal.Listlike {
    public GLib.List<weak Val> vs;
    public List(GLib.List<Val> values) {
        foreach (var value in values) {
            vs.append(value);
        }
    }
    public List.empty() {
    }
    public override Mal.Iterator iter() {
        return new Mal.ListIterator(this);
    }
    public override Mal.ValWithMetadata copy() {
        var result = new Mal.List.empty();
        result.vs = vs.copy();
        return result;
    }        
}

class Mal.ListIterator : Mal.Iterator {
    // This reference ensures the container is collected after the iterator.
    private Mal.List container;
    private weak GLib.List<weak Val>? node;
    public ListIterator(Mal.List container_) {
        container = container_;
        node = container_.vs;
    }
    public override Mal.Val? deref() {
        return node == null ? null : node.data;
    }
    public override Mal.Iterator step() {
        if (node != null)
            node = node.next;
        return this;
    }
}

class Mal.Vector : Mal.Listlike {
    struct Ref { weak Mal.Val v; }
    private Ref[] rs;
    public Vector.with_size(uint size) {
        rs = new Ref[size];
    }
    public override Mal.Iterator iter() {
        return new Mal.VectorIterator(this);
    }
    public override Mal.ValWithMetadata copy() {
        var copied = new Vector();
        copied.rs = rs;
        return copied;
    }
    public uint length { get { return rs.length; } }
    public new Mal.Val @get(uint pos) {
        assert(pos < rs.length);
        return rs[pos].v;
    }
    public new void @set(uint pos, Mal.Val v) {
        assert(pos < rs.length);
        rs[pos].v = v;
    }
}

class Mal.VectorIterator : Mal.Iterator {
    // This reference ensures the container is collected after the iterator.
    private Mal.Vector vec;
    private int pos;
    public VectorIterator(Mal.Vector container_) {
        vec = container_;
        pos = 0;
    }
    public override Mal.Val? deref() {
        return pos >= vec.length ? null : vec[pos];
    }
    public override Mal.Iterator step() {
        if (pos < vec.length) pos++;
        return this;
    }
}

class Mal.Num : Mal.Hashable {
    public int64 v;
    public Num(int64 value) {
        v = value;
        hashkey = "N" + v.to_string();
    }
}

abstract class Mal.SymBase : Mal.Hashable {
    public string v;
}

class Mal.Sym : Mal.SymBase {
    public Sym(string value) {
        v = value;
        hashkey = "'" + v;
    }
}

class Mal.Keyword : Mal.SymBase {
    public Keyword(string value) {
        v = value;
        hashkey = ":" + v;
    }
}

class Mal.String : Mal.Hashable {
    public string v;
    public String(string value) {
        v = value;
        hashkey = "\"" + v;
    }
}

class Mal.Hashmap : Mal.ValWithMetadata {
    public GLib.HashTable<weak Mal.Hashable, weak Mal.Val> vs;
    construct {
        vs = new GLib.HashTable<weak Mal.Hashable, weak Mal.Val>(
            Mal.Hashable.hash, Mal.Hashable.equal);
    }
    public void insert(Mal.Val key, Mal.Val value) throws Mal.Error {
        var hkey = key as Mal.Hashable;
        if (hkey == null)
            throw new Error.HASH_KEY_TYPE_ERROR("bad type as hash key");
        vs[hkey] = value;
    }
    public void remove(Mal.Val key) throws Mal.Error {
        var hkey = key as Mal.Hashable;
        if (hkey == null)
            throw new Error.HASH_KEY_TYPE_ERROR("bad type as hash key");
        vs.remove(hkey);
    }
    public override Mal.ValWithMetadata copy() {
        var toret = new Mal.Hashmap();
        toret.vs = vs;
        return toret;
    }        
    public override void gc_traverse() {
        base.gc_traverse();
        foreach (var key in vs.get_keys()) {
            key.visit();
            vs[key].visit();
        }
    }
}

abstract class Mal.BuiltinFunction : Mal.ValWithMetadata {
    public abstract string name();
    public abstract Mal.Val call(Mal.Val[] args) throws Mal.Error;
    public void check_arg_count(uint expected, Mal.Val[] got) throws Mal.Error {
        if (got.length != expected)
            throw new Mal.Error.BAD_PARAMS
                ("%s: expected %u argument(s), got: '%s'",
                 name(), expected, pr_list(got, true, " "));
    }
}

class Mal.Function : Mal.ValWithMetadata {
    public bool is_macro;
#if !NO_ENV
    public string[] parameters;
    public weak Mal.Val body;
    public weak Mal.Env env;
    public Function(string[] parameters_, Mal.Val body_, Mal.Env env_) {
        parameters = parameters_;
        body = body_;
        env = env_;
        is_macro = false;
    }
#endif
    public override Mal.ValWithMetadata copy() {
#if !NO_ENV
        var copied = new Mal.Function(parameters, body, env);
        copied.is_macro = is_macro;
        return copied;
#else
        assert(false);
        return new Mal.Nil(); // Silent a warning
#endif
    }
    public override void gc_traverse() {
        base.gc_traverse();
#if !NO_ENV
        body.visit();
        env.visit();
#endif
    }
}

class Mal.Atom : Mal.Val {
    public weak Mal.Val v;
    public Atom(Mal.Val v_) { v = v_; }
    public override void gc_traverse() {
        base.gc_traverse();
        v.visit();
    }
}
