include ../../steps.mk

all: $(step0A)

zig_opts += --release=safe
zig_opts += -Doptimize=Debug
$(step0A):
	zig build $(zig_opts) -Dname=$@ -Droot_source_file=$@.zig

.PHONY: all $(step0A) clean

clean:
	rm -fr .zig-cache/ zig-out/
	rm -f *~
