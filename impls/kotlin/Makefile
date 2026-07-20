include ../../steps.mk

SOURCES_BASE = reader.kt printer.kt types.kt env.kt core.kt readline.kt

all: $(step0A:=.jar)

dist: mal.jar mal

mal.jar: stepA_mal.jar
	cp $< $@

SHELL := bash
mal: mal.jar
	cat <(echo -e '#!/bin/sh\nexec java -jar "$$0" "$$@"') mal.jar > $@
	chmod +x mal

clean:
	rm -vf $(step0A:=.jar) mal.jar mal

$(step0A:=.jar): %.jar: src/mal/%.kt $(SOURCES_BASE:%.kt=src/mal/%.kt)
	kotlinc $^ -include-runtime -d $@
