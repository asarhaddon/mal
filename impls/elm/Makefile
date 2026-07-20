include ../../steps.mk

ELM = node_modules/.bin/elm

all: node_modules $(step0A:=.js)

node_modules:
	npm install

$(step0A:=.js): s%.js: src/S%.elm node_modules
	$(ELM) make $< --output $@

$(step0A:=.js): src/IO.elm
$(step1A:=.js): src/Reader.elm
$(step1A:=.js): src/Printer.elm
$(step1A:=.js): src/Utils.elm
$(step1A:=.js): src/Types.elm
$(step1A:=.js): src/Env.elm
$(step4A:=.js): src/Core.elm
$(step4A:=.js): src/Eval.elm

clean:
	rm -f $(step0A:=.js)
