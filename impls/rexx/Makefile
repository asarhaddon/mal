include ../../steps.mk

PREPROCESSED = $(step0A:=.rexxpp)

all: $(PREPROCESSED) dist

dist: mal

mal: mal.rexxpp
	echo "#!/usr/bin/rexx -a" > $@
	cat $< >> $@
	chmod +x $@

mal.rexxpp: stepA_mal.rexxpp
	cp -a $+ $@

$(PREPROCESSED): %.rexxpp: %.rexx readline.rexx types.rexx reader.rexx printer.rexx env.rexx core.rexx
	cpp -CC -P -nostdinc $< > $@

clean:
	rm -f mal.rexx mal *.rexxpp

.PHONY: all dist clean
