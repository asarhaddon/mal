include ../../steps.mk

all: $(step0A)

obj:
	mkdir obj

# stepA_mal is awkward because GNAT requires the filename to be lowercase
$(step0A): | obj
	gnatmake -O3 -gnata $(subst A,a,$@).adb -D obj -o $@
# Delegate the dependency handling to gnatmake.
.PHONY: $(step0A)

clean:
	rm -f $(step0A)
	rm -rf obj
