include ../../steps.mk
#
scheme_MODE ?= chibi

# Chicken requires reader, printer after util, types.
deps1 := util types reader printer
deps3 := env
deps4 := core
deps := $(deps1) $(deps3) $(deps4)

ifeq ($(scheme_MODE),kawa)
KAWALIB = kawa --r7rs --no-warn-unused -d out -C
KAWA = kawa --r7rs --no-warn-unused -d out --main -C
  all: $(step0A:%=out/%.class)
  $(step0A:%=out/%.class): out/%.class: %.scm
	$(KAWA) $<
  $(step1A:%=out/%.class): $(deps1:%=out/lib/%.class)
  $(step3A:%=out/%.class): $(deps3:%=out/lib/%.class)
  $(step4A:%=out/%.class): $(deps4:%=out/lib/%.class)
  $(deps:%=out/lib/%.class): out/lib/%.class: lib/%.scm
	$(KAWALIB) $<
  $(deps:%=lib/%.scm): lib/%.scm:
	ln -s $*.sld $@

else ifeq ($(scheme_MODE),chicken)
CHICKEN = csc -setup-mode -host -O3 -R r7rs
CHICKENLIB = $(CHICKEN) -D compiling-extension -J -s -regenerate-import-libraries
  all: $(step0A)
  $(step0A): %: %.scm
	$(CHICKEN) $<
  $(step1A): $(deps1:%=lib.%.so)
  $(step3A): $(deps3:%=lib.%.so)
  $(step4A): $(deps4:%=lib.%.so)
  $(deps:%=lib.%.so): lib.%.so: lib/%.sld
	$(CHICKENLIB) $< -o $@

else ifeq ($(scheme_MODE),cyclone)
CYCLONELIB = cyclone -O2
CYCLONE = $(CYCLONELIB)
  all: $(step0A)
  $(step0A): %: %.scm
	$(CYCLONE) $<
  $(step1A): $(deps1:%=lib/%.so)
  $(step3A): $(deps3:%=lib/%.so)
  $(step4A): $(deps4:%=lib/%.so)
  $(deps:%=lib/%.so): %.so: %.sld
	$(CYCLONELIB) $<

# chibi gauche sagittarius foment are interpreted
endif

RM = rm -f
RMR = rm -rf

.PHONY: clean

clean:
	$(RM) lib/*.scm lib/*.so lib/*.c lib/*.o lib/*.meta
	$(RM) lib.*.scm *.build.sh *.install.sh *.link *.so *.c *.o $(step0A)
	$(RMR) out
