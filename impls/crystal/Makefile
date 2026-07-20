include ../../steps.mk

all: $(step0A)
$(step0A):
	shards build $@ --release
clean:
	rm -rf .cache/crystal/ .cache/shards/ bin/ lib/
.PHONY: all clean $(step0A)
