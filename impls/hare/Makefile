include ../../steps.mk
#
CC= hare build

.PHONY: all
all: $(step0A)

$(step0A): %: %.ha $(wildcard mal/*.ha)
	$(CC) -o $@ $<

.PHONY: clean
clean:
	rm $(step0A)
