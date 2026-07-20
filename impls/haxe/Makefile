include ../../steps.mk
#
STEP1_DEPS = Compat.hx types/Types.hx reader/Reader.hx printer/Printer.hx
STEP3_DEPS = env/Env.hx
STEP4_DEPS = core/Core.hx

haxe_MODE ?= neko

# Neko target (neko)

ifeq (neko,$(haxe_MODE))
all: $(step0A:=.n)

$(step0A:=.n): s%.n: S%.hx
	haxe -main S$* -neko $@

$(step1A:=.n): $(STEP1_DEPS)
$(step3A:=.n): $(STEP3_DEPS)
$(step4A:=.n): $(STEP4_DEPS)

mal: mal.n
	nekotools boot $<
	chmod +x $@
mal.n: stepA_mal.n
	cp $< $@


# Python 3 target (python)

else ifeq (python,$(haxe_MODE))
all: $(step0A:=.py)

$(step0A:=.py): s%.py: S%.hx
	haxe -main S$* -python $@

$(step1A:=.py): $(STEP1_DEPS)
$(step3A:=.py): $(STEP3_DEPS)
$(step4A:=.py): $(STEP4_DEPS)

mal: $(stepA).py
	(echo '#!/usr/bin/env python3'; cat $<) > $@
	chmod +x $@


# C++ target (cpp)

else ifeq (cpp,$(haxe_MODE))
all: $(step0A:%=cpp/%)

$(step0A:%=cpp/%): cpp/s%: S%.hx
	haxe -main S$* -cpp cpp
	cp cpp/S$* $@

$(step1A:%=cpp/%): $(STEP1_DEPS)
$(step3A:%=cpp/%): $(STEP3_DEPS)
$(step4A:%=cpp/%): $(STEP4_DEPS)

mal: cpp/$(stepA)
	cp $< $@
	chmod +x $@


# JavaScript target (js)

else ifeq (js,$(haxe_MODE))
all: $(step0A:=.js)

$(step0A:=.js): s%.js: S%.hx
	haxe -main S$* -js $@

$(step0A:=.js): node_readline.js node_modules
$(step1A:=.js): $(STEP1_DEPS)
$(step3A:=.js): $(STEP3_DEPS)
$(step4A:=.js): $(STEP4_DEPS)

node_modules:
	npm install

mal:
	(echo "#!/usr/bin/env node"; cat $<) > $@
	chmod +x $@

###

else
  $(error Invalid haxe_MODE=$(haxe_MODE))
endif

clean:
	rm -f mal.n mal.py cpp/mal mal.js mal
	rm -f $(step0A:=.py) $(step0A:=.js) $(step0A:=.n)
	rm -fr cpp
