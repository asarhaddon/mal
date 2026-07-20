include ../../steps.mk

SOURCES_BASE = util.sk types.sk reader.sk printer.sk

all: $(step0A:=.js) dist

dist: mal

$(step0A:=.js): $(SOURCES_BASE) env.sk
$(step4A:=.js): core.sk

$(step0A:=.js): %.js: %.sk
	skewc --target=js --release --output-file=$@ $^

mal: stepA_mal.js
	echo "#!/usr/bin/env node" > $@
	cat $< >> $@
	chmod +x $@

clean:
	rm -rf step*.js mal

.PHONY: all dist clean
