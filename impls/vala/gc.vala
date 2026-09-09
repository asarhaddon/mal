abstract class GC.Object : GLib.Object {
    public bool visited;

    construct {
        visited = false;
        GC.Core.register_object(this);
    }

    public void visit() {
        if (!visited) {
            visited = true;
            gc_traverse();
        }
    }

    public virtual void gc_traverse() { }
    // Should call the method of the base/super/parent class, then
    // call ref.visit() on each pointer `ref` to a GC.Object the
    // current instance is holding.
}

class GC.Core : GLib.Object {
    private static Object objects[1000000];
    private static uint objects_count = 0;
    // Between two collections, indices from 0 to objects_count - 1
    // refer to all created Mal.Object instances.

    // collect() traverses the list, and erases the element which are
    // the last reference to the instance (triggering the normal
    // deallocation because of a zero reference count).

    // maybe_collect() triggers a collection when objects_count exceeds
    // until_next_collection, which is twice the objects_count right
    // after last collection.
    private static uint until_next_collection = 0;

    public static void register_object(GC.Object obj) {
        // If this ever fails, increase the size of the objects array.
        assert(objects_count < objects.length);
        objects[objects_count++] = obj;
    }

    public static void collect() {
        uint remaining = 0;

#if GC_STATS
        uint roots = 0;
#endif

#if GC_DEBUG
        stderr.printf("GC: started\n");
        for (uint i = 0; i < objects_count; ++i)
            assert(!objects[i].visited);
#endif

        for (uint i = 0; i < objects_count; ++i)
            if (1 < objects[i].ref_count) {
#if GC_STATS
                roots++;
#endif
                objects[i].visit();
            }
#if GC_DEBUG
        //  Do a separate round now so that the objects can be printed
        //  recursively.  During the deallocation, references owned by
        //  an object may already be deallocated.
        for (uint i = 0; i < objects_count; ++i) {
            string state;
            if (objects[i].visited) {
                if (1 < objects[i].ref_count)
                    state = "root";
                else
                    state = "visited";
            } else {
                assert(objects[i].ref_count == 1);
                state = "collected";
            }
            unowned var val = objects[i] as Mal.Val; // do not change refcount
            string image;
            if (val == null)
                image = Type.from_instance(objects[i]).name();
            else
                image = Mal.pr_str(val);
            stderr.printf("GC: %p rc=%2u %-9s %s\n", objects[i],
                          objects[i].ref_count, state, image);
        }
#endif
        for (uint i = 0; i < objects_count; ++i)
            if (objects[i].visited) {
                objects[i].visited = false; // prepare next collection
                if (remaining < i) {
                    objects[remaining] = objects[i];
                    objects[i] = null;
                }
                ++remaining;
            } else
                objects[i] = null;

#if GC_DEBUG
        stderr.printf("GC: finished\n");
#endif

#if GC_STATS
        stderr.printf("GC: %u roots, %u -> %u objects\n",
                      roots, objects_count, remaining);
#endif

        objects_count = remaining;
        until_next_collection = remaining << 1;
    }

    public static void maybe_collect() {
#if !GC_ALWAYS
        if (objects_count < until_next_collection)
            return;
#endif
        collect();
    }
}
