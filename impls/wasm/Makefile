include ../../steps.mk

MODE ?= $(strip \
          $(if $(filter wace_libc,$(wasm_MODE)),\
	    libc,\
	    $(if $(filter direct node js wace_fooboot warpy,$(wasm_MODE)),\
	      direct,\
	      wasi)))

EXT = .wasm

WASM_AS ?= wasm-as
WAMP ?= node_modules/.bin/wamp

all: $(step0A:=$(EXT))

$(WAMP):
	npm install

$(step0A:=.wat): %.wat: %.wam
	$(WAMP) $(filter %.wam,$^) > $*.wat

$(step0A:=.wasm): %.wasm: %.wat
	$(WASM_AS) $< -o $@

$(step0A:=.wat): $(WAMP) platform_$(MODE).wam string.wam printf.wam
$(step1A:=.wat): types.wam mem.wam debug.wam reader.wam printer.wam
$(step3A:=.wat): env.wam
$(step4A:=.wat): core.wam

.PHONY: clean

clean:
	rm -f *.wat *.wasm
