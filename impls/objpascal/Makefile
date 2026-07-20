include ../../steps.mk

#####################

DEBUG = -gl

# Set this to link with libreadline instead of libedit
USE_READLINE =

FPC = fpc -MOBJFPC -ve -Furegexpr/Source $(DEBUG) $(if $(strip $(USE_READLINE)),-dUSE_READLINE,)

all: $(step0A)

$(step0A): %: %.pas
	$(FPC) $<

$(step0A): mal_readline.pas
$(step1A): mal_types.pas reader.pas printer.pas
$(step3A): mal_env.pas
$(step4A): core.pas

clean:
	rm -f $(step0A) *.o *.ppu regexpr/Source/*.o regexpr/Source/*.ppu mal
