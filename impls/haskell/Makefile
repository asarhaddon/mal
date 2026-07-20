include ../../steps.mk

ghc_flags = -Wall -Wextra
LDLIBS = -lreadline

#####################

all: $(step0A)

$(step0A): %: %.hs
	ghc ${ghc_flags} --make $< $(LDLIBS) -o $@

$(step0A): Readline.hs
$(step1A): Types.hs Reader.hs Printer.hs
$(step3A): Env.hs
$(step4A): Core.hs

clean:
	rm -f $(step0A) *.hi *.o
