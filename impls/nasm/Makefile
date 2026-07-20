include ../../steps.mk

COMPONENTS = env.asm core.asm reader.asm printer.asm types.asm system.asm exceptions.asm


all: $(step0A)

$(step0A:=.o): %.o: %.asm $(COMPONENTS)
	nasm -felf64 $<

$(step0A): %: %.o
	ld -o $@ $<

.PHONY: clean
clean:
	rm -f $(step0A) $(step0A:=.o)
