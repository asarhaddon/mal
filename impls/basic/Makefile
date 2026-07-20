include ../../steps.mk

basic_MODE = cbm
BASICPP_OPTS = --mode $(basic_MODE)

FBC = fbc -lang qb

ifeq (qbasic,$(basic_MODE))
  all: $(step0A)
else
  all: $(step0A:=.bas)
endif

$(step0A:=.bas): debug.in.bas mem.in.bas readline.in.bas
$(step1A:=.bas): types.in.bas reader.in.bas printer.in.bas
$(step3A:=.bas): env.in.bas
$(step4A:=.bas): core.in.bas


$(step0A:=.bas): %.bas: %.in.bas
	./basicpp.py $(BASICPP_OPTS) $< > $@

tests/%.bas: tests/%.in.bas
	./basicpp.py $(BASICPP_OPTS) $< > $@

# QBasic specific compilation rule
$(step0A): %: %.bas
	$(FBC) $< -x $@

# CBM/C64 image rules

$(step0A:=.prg): %.prg: %.bas
	cat $< | tr "A-Z" "a-z" > $<.tmp
	#cat $< | sed 's/["]\@<!\<\w\+\>["]\@!/\L&/g' > $<.tmp
	petcat -w2 -nc -o $@ $<.tmp
	#rm $<.tmp

mal.prg: stepA_mal.prg
	cp $< $@

.args.mal.prg: .args.mal
	petcat -text -w2 -o $@ $<

core.mal.prg: ../core.mal
	petcat -text -w2 -o $@ $<

mal.d64: mal.prg .args.mal.prg core.mal.prg
	c1541 -format "mal,01" d64 $@ \
	    -attach $@ \
	    -write $< mal \
	    -write .args.mal.prg .args.mal \
	    -write core.mal.prg core.mal


# Clean and Stats rules

.PHONY: clean

clean:
	rm -f $(step0A:=.bas) $(step0A) *.d64 *.prg
	rm -rf ./internal
