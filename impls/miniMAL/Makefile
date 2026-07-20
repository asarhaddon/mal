include ../../steps.mk

SOURCES_BASE = node_readline.js miniMAL-core.json \
	       types.json reader.json printer.json
SOURCES_LISP = env.json core.json stepA_mal.json
SOURCES = $(SOURCES_BASE) $(SOURCES_LISP)

all: node_modules

node_modules:
	npm install

$(step4A:=.json): node_modules

dist: mal.json mal

mal.json: $(filter-out %.js,$(SOURCES))
	echo '["do",' >> $@
	$(foreach f,$+,\
	  cat $(f) | egrep -v '^ *[[]"load-file"' >> $@; \
	  echo "," >> $@;)
	echo 'null]' >> $@

mal: mal.json
	echo '#!/usr/bin/env miniMAL' > $@
	cat $< >> $@
	chmod +x $@

clean:
