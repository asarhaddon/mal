include ../../steps.mk

ifdef DEBUG
  ADAFLAGS := -Wall -Wextra -gnatw.eH.Y -gnatySdouxy -gnatVa -g -gnataEfoqQ \
    -fstack-check -pg
  LDFLAGS  := -pg
else
  # -O3 is not recommended as the default by the GCC documentation,
  # and -O2 seems to produce slightly better performances.
  ADAFLAGS := -O2 -gnatnp
endif

# Compiler arguments.
CARGS = $(ADAFLAGS)
# Linker arguments.
LARGS = $(LDFLAGS) -lreadline

.PHONY: all clean
all: $(step0A)
clean:
	$(RM) *~ *.adt *.ali *.o b~*.ad[bs] gmon.out $(step0A)

# Tell Make how to detect out-of-date executables, and let gnatmake do
# the rest when it must be executed.
$(step09): %: %.adb
$(stepA): stepa_mal.adb
$(step1A): envs.adb envs.ads
$(step1A): err.adb err.ads
$(step1A): garbage_collected.adb garbage_collected.ads
$(step1A): printer.adb printer.ads
$(step1A): reader.adb reader.ads
$(step1A): readline.adb readline.ads
$(step1A): types.adb types.ads
$(step1A): types-atoms.adb types-atoms.ads
$(step1A): types-builtins.adb types-builtins.ads
$(step1A): types-fns.adb types-fns.ads
$(step1A): types-maps.adb types-maps.ads
$(step1A): types-sequences.adb types-sequences.ads
$(step1A): types-strings.adb types-strings.ads
$(step4A): core.adb core.ads
$(step0A):
	gnatmake $< -o $@ -cargs $(CARGS) -largs $(LARGS)
