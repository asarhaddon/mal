include ../../steps.mk

OTHER_SRCS = pkg_readline.vhdl types.vhdl printer.vhdl reader.vhdl env.vhdl core.vhdl
OTHER_OBJS = $(OTHER_SRCS:%.vhdl=%.o)

#####################

all: $(step0A)

dist: mal

mal: $(stepA)
	cp $< $@

work-obj93.cf: $(OTHER_SRCS)
	rm -f work-obj93.cf
	ghdl -i $+

$(OTHER_OBJS): work-obj93.cf
$(step0A:=.o): $(OTHER_OBJS)
$(OTHER_OBJS) $(step0A:=.o): %.o: %.vhdl
	ghdl -a -g $<

$(step0A): $(OTHER_OBJS)
$(step0A): %: %.o
	ghdl -e -g $@
	# ghdl linker creates a lowercase executable; rename it to stepA_mal
	if [ "$@" = "stepA_mal" ]; then mv stepa_mal $@; fi

clean:
	rm -f *.o $(step0A) work-obj93.cf mal
