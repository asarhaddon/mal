include ../../steps.mk

CC = gcc

CFLAGS = -std=c99 -g -Wall -Wextra -fanalyzer

# The code defines new format specifiers.
CPPFLAGS = -Wno-format

ifdef debug_reader
  CPPFLAGS += -DDEBUG_READER
endif
ifdef debug_hash
  CPPFLAGS += -DDEBUG_HASH
endif
ifdef debug_hashmap
  CPPFLAGS += -DDEBUG_HASHMAP
endif
ifdef debug_hash_collisions
  CPPFLAGS += -DDEBUG_HASH_COLLISIONS
endif
ifndef no_fast
  CFLAGS  += -flto -O3 -DNDEBUG
  LDFLAGS += -flto
endif
ifdef profile
  CFLAGS  += -pg
  LDFLAGS += -pg
endif
ifdef readline
  pkgconfig_modules += readline
  CFLAGS += -DUSE_READLINE
else
  pkgconfig_modules += libedit
endif
ifndef no_ffi
  pkgconfig_modules += libffi
  CFLAGS += -DWITH_FFI
endif

pkgconfig_modules += bdw-gc
CFLAGS += $(shell pkg-config --cflags $(pkgconfig_modules))
LDLIBS += $(shell pkg-config --libs   $(pkgconfig_modules))

all: $(step0A)

# GCC could create temporary objects files, but separate recipes for
# .o objects give faster build cycles when debugging.
$(step0A): readline.o
$(step1A): error.o hashmap.o linked_list.o printer.o reader.o types.o vector.o
$(step3A): env.o
$(step4A): core.o

include deps
deps:
	$(CC) -MM -MF- *.c > $@

clean:
	rm -f $(step0A) *.o deps gmon.out

.PHONY: all clean
