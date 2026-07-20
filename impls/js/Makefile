include ../../steps.mk

TESTS = tests/types.js tests/reader.js

SOURCES_BASE = node_readline.js types.js reader.js printer.js interop.js
SOURCES_LISP = env.js core.js stepA_mal.js
SOURCES = $(SOURCES_BASE) $(SOURCES_LISP)
WEB_SOURCES = $(SOURCES:node_readline.js=jq_readline.js)

all: node_modules

dist: mal.js mal web/mal.js

node_modules:
	npm install

$(step0A:=.js): node_modules

mal.js: $(SOURCES)
	cat $+ | grep -v "= *require('./" >> $@

mal: mal.js
	echo "#!/usr/bin/env node" > $@
	cat $< >> $@
	chmod +x $@

web/mal.js: $(WEB_SOURCES)
	cat $+ | grep -v "= *require('./" > $@

clean:
	rm -f mal.js web/mal.js
	rm -rf node_modules

.PHONY: tests $(TESTS)

tests: $(TESTS)

$(TESTS):
	@echo "Running $@"; \
	node $@ || exit 1; \
