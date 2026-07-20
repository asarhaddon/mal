include ../../steps.mk

# No TCO in this implementation.
step5 :=

sml_MODE_DEFAULT = polyml
sml_MODE_CONFIG  = .smlmode

ifeq ($(sml_MODE),)
sml_MODE = $(sml_MODE_DEFAULT)
endif
# some hackery to let Make know if it needs to rebuild when sml_MODE changes
ifneq ($(sml_MODE),$(shell cat $(sml_MODE_CONFIG) 2> /dev/null))
$(shell rm $(sml_MODE_CONFIG) 2> /dev/null)
endif

all: $(step0A)

dist: mal

mal: stepA_mal
	cp $< $@

$(step0A:%=.%.dep): .%.dep: %.mlb
	@echo sml-deps -o $@ $<
	$(eval DEPS := $(shell grep '[.]sml' $<))
	@echo "$(@:.%.dep=%) $@: $(DEPS)" > $@

include $(step0A:%=.%.dep)

$(step0A:%=.%.poly.sml): .%.poly.sml: %.mlb
	@echo generate-sml -o $@ $<
	@grep '[.]sml' $< | grep -v main | xargs printf 'use "%s";\n' > $@

# some hackery to let Make track changes in sml_MODE
$(sml_MODE_CONFIG):
	@echo $(sml_MODE) > $@

ifeq ($(sml_MODE),mlton)
  $(step0A): %: %.mlb $(sml_MODE_CONFIG)
	mlton -output $@ $<
else ifeq ($(sml_MODE),mosml)
  $(step0A): %: %.mlb $(sml_MODE_CONFIG)
	mosmlc -o $@ LargeInt.sml -toplevel `grep '[.]sml' $<`
else ifeq ($(sml_MODE),polyml)
  $(step0A): %: .%.poly.sml $(sml_MODE_CONFIG)
	polyc -o $@ $<
else
  $(error Unknown sml_MODE: $(sml_MODE))
endif

clean:
	rm -f $(step0A) .*.dep *.ui *.uo .*.poly.sml $(sml_MODE_CONFIG)

.PHONY: all clean
