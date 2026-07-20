include ../../steps.mk

SOURCES_BASE = node_readline.js types.mjs reader.mjs printer.mjs
SOURCES_LISP = env.mjs core.mjs stepA_mal.mjs
SOURCES = $(SOURCES_BASE) $(SOURCES_LISP)

all: node_modules

dist: mal.js mal

node_modules:
	npm install

$(step0A:=.mjs): node_modules

mal.js: $(SOURCES)
	cat $+ | sed 's/^export //' | grep -v "^import " >> $@

mal: mal.js
	echo "#!/usr/bin/env node" > $@
	cat $< >> $@
	chmod +x $@


clean:
	rm -f mal.js mal
	rm -rf node_modules
