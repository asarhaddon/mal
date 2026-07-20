include ../../steps.mk

# From: https://blog.tlensing.org/2013/02/24/objective-c-on-linux-setting-up-gnustep-clang-llvm-objective-c-2-0-blocks-runtime-gcd-on-ubuntu-12-04/:
#   clang `gnustep-config --objc-flags` -o main -x objective-c main.m -fconstant-string-class=NSConstantString -fobjc-nonfragile-abi -fblocks -lgnustep-base -lgnustep-gui -ldispatch -I/usr/local/include/GNUstep -L/usr/local/lib/GNUstep

OS := $(shell uname)

## Bizzare gnustep-config/make interaction causes make to get run
## during gnustep-config so we need to remove make output
ifeq ($(OS),Darwin)
CC = clang -framework Foundation
OBJC_LIBS := -lobjc -lreadline
else
#CC = clang -fblocks -fobjc-nonfragile-abi -fobjc-arc
CC = clang -fblocks -fobjc-nonfragile-abi
OBJC_FLAGS := $(shell gnustep-config --objc-flags 2>/dev/null | egrep -v "Entering|Leaving")
OBJC_LIBS := $(filter-out -shared-libgcc,$(shell gnustep-config --base-libs 2>/dev/null | egrep -v "Entering|Leaving")) -ldispatch -lreadline
endif

all: $(step0A)

dist: mal

mal: stepA_mal
	cp $< $@

$(step0A): mal_readline.c mal_readline.h
$(step1A): types.h types.m reader.h reader.m printer.h printer.m
$(step3A): env.m
$(step4A): malfunc.h malfunc.m core.h core.m

$(step0A): step%: step%.m
	$(CC) \
	    -xobjective-c $(filter-out %.h mal_readline%,$+) \
	    -xc mal_readline.c \
	    -o $@ \
	    $(OBJC_FLAGS) \
	    $(OBJC_LIBS)

clean:
	rm -f $(step0A) *.o *.d mal
