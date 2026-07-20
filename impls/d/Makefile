include ../../steps.mk

d_MODE ?= gdc

D ?= $(d_MODE)

ifeq ($(D),gdc)
CFLAGS += -g -O2 -Wall
LDFLAGS += -lreadline
OF = -o $@
else ifeq ($(D),ldc2)
CFLAGS += -g -O2
LDFLAGS += -L-lreadline
OF = -of $@
else ifeq ($(D),dmd)
CFLAGS += -g -O
LDFLAGS += -L-lreadline
OF = -of=$@
else
	@echo "Unsupported D implementation $(D)"
	@exit 1
endif

#####################

EARLY_OBJS = types.o readline.o reader.o printer.o env.o
deps3A := mal_core.o

#####################

all: $(step0A)

dist: mal

mal: $(stepA)
	cp $< $@

$(step0A:=.o) $(EARLY_OBJS) $(deps3A): %.o: %.d
	$(D) $(CFLAGS) -c $< $(OF)

$(step0A): $(EARLY_OBJS)
$(step3A): $(deps3A)

$(step0A): %: %.o
	$(D) $+ $(OF) $(LDFLAGS)

clean:
	rm -f *.o $(step0A) mal
