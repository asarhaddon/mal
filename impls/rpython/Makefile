include ../../steps.mk

RPYTHON = rpython

all: $(step0A)

dist: mal

mal: stepA_mal
	cp $< $@

$(step0A): %: %.py
	$(RPYTHON) --output=$@ $<

$(step0A): mal_readline.py
$(step1A): mal_types.py reader.py printer.py
$(step3A): env.py
$(step4A): core.py

.PHONY: clean

clean:
	rm -f mal $(step0A) *.pyc
	rm -rf __pycache__

