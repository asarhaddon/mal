include ../../steps.mk

#####################

SOURCES_BASE = src/types/types.go src/readline/readline.go \
	       src/reader/reader.go src/printer/printer.go \
	       src/env/env.go src/core/core.go

#####################

all: $(step0A)

dist: mal

mal: $(stepA)
	cp $< $@

$(step0A): $(SOURCES_BASE)
	go build -o $@ ./src/$@
$(foreach b,$(step0A),$(eval $(b): src/$(b)/$(b).go))


clean:
	rm -f $(step0A) mal
