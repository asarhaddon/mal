include ../../steps.mk

# Inhibit default make rules, in case they try to build from leftover .c files
.SUFFIXES:

all: $(step0A)

# You can define VFLAGS on the command line to add flags to the vala compiler.
# Some useful ones:
#
#  -g        annotate the output C with #line directives so that backtraces
#            from gdb, sanitisers and valgrind will list Vala source locations
#
#  -X -g -X -O0    compile the output C for sensible debugging
#
#  -X -fsanitize=address    link the output program against Address Sanitizer
#
#  --save-temps    don't automatically delete the C files after compiling
#
#  -D GC_STATS     print statistics every time the garbage collector runs
#
#  -D GC_DEBUG     print full diagnostics from the garbage collector
#
#  -D GC_ALWAYS    make the garbage collector run at every opportunity
#                  (good for making occasional GC errors show up sooner)

$(step0A): %: %.vala
	valac $(VFLAGS) -o $@ $^ $(DEFINES) --pkg readline -X -lreadline

$(step1) $(step2): override DEFINES += -D NO_ENV

$(step1A): gc.vala types.vala reader.vala printer.vala
$(step3A): env.vala
$(step4A): core.vala

clean: clean-c
	rm -f $(step0A)

clean-c:
	rm -f *.c *.h
