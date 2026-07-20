include ../../steps.mk

MODULES = types.ml reader.ml printer.ml env.ml core.ml
LIBS = str.cmxa unix.cmxa
MAL_LIB = mal_lib.cmxa
# Apparently necessary with caml 5.0:
OPTIONS = -I +str -I +unix

all: $(step0A)

dist: mal

mal: $(stepA)
	cp $< $@

# ocaml repl apparently needs bytecode, not native, compilation.
# Just do it all right here:
repl:
	ocamlc -c $(LIBS:%.cmxa=%.cma) $(MODULES) $(step0A:=.ml)
	rlwrap ocaml $(LIBS:%.cmxa=%.cma) $(MODULES:%.ml=%.cmo)

$(MAL_LIB): $(MODULES)
	ocamlopt -a $(MODULES) -o $@ $(OPTIONS)

$(step0A): %: %.ml $(MAL_LIB)
	ocamlopt $(LIBS) $(MAL_LIB) $< -o $@ $(OPTIONS)

clean:
	rm -f $(step0A) mal mal_lib.* *.cmo *.cmx *.cmi *.o

format:
	ocamlformat --inplace --enable-outside-detected-project *.ml
.PHONY: all repl clean format
