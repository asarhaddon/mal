include ../../steps.mk

#####################

SOURCES_BASE = types.nim reader.nim printer.nim
SOURCES_REBUILD = $(SOURCES_BASE) env.nim core.nim

#####################

all: $(step0A)

dist: mal

mal: $(stepA)
	cp $< $@

$(step0A): %: %.nim $(SOURCES_REBUILD)
	nim -d:release --nimcache:nimcache-$@ c $@

clean:
	rm -rf nimcache-*/ $(step0A)
	rm -f mal
