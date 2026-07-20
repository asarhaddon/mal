include ../../steps.mk

#####################

SOURCES_BASE = src/atom.erl src/printer.erl src/reader.erl
SOURCES_LISP = src/core.erl src/env.erl src/types.erl src/stepA_mal.erl
SOURCES = $(SOURCES_BASE) $(SOURCES_LISP)

#####################

.PHONY: all dist clean

all: $(step0A)

dist: mal

mal: $(SOURCES)
	sed 's/stepA_mal/mal/' src/stepA_mal.erl > src/mal.erl
	MAL_STEP=mal rebar compile escriptize
	rm src/mal.erl

.PHONY: $(step0A)
$(step0A): %: src/%.erl
	MAL_STEP=$* rebar compile escriptize

clean:
	rebar clean
	rm -f mal
