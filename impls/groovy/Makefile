include ../../steps.mk

CLASSES = types.class reader.class printer.class env.class core.class

all: ${CLASSES}

dist: mal.jar

$(step1A:=.groovy): types.class reader.class printer.class
$(step3A:=.groovy): env.class
$(step4A:=.groovy): core.class

$(CLASSES): %.class: %.groovy
	groovyc $<

core.class: types.class reader.class printer.class

mal.jar: ${CLASSES}
	groovyc stepA_mal.groovy
	GROOVY_HOME=/usr/share/groovy groovy GroovyWrapper -d $@ -m stepA_mal

SHELL := bash
mal: mal.jar
	cat <(echo -e '#!/bin/sh\nexec java -jar "$$0" "$$@"') mal.jar > $@
	chmod +x mal

clean:
	rm -f *.class classes/* mal.jar mal
	rmdir classes || true
