step0 := step0_repl
step1 := step1_read_print
step2 := step2_eval
step3 := step3_env
step4 := step4_if_fn_do
step5 := step5_tco
step6 := step6_file
step7 := step7_quote
step8 := step8_macros
step9 := step9_try
stepA := stepA_mal

step0A = $(step0) $(step1A)
step1A = $(step1) $(step2) $(step3A)
step3A = $(step3) $(step4A)
step4A = $(step4) $(step5) $(step6) $(step7) $(step8) $(step9) $(stepA)

uname_S != uname -s 2>/dev/null

CXX=g++
ifeq ($(uname_S),Darwin)
	# Native build on yosemite. Requires: brew install readline
	READLINE=/usr/local/opt/readline
	INCPATHS=-I$(READLINE)/include
	LIBPATHS=-L$(READLINE)/lib
endif

LINK.o = $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(LDFLAGS)

DEBUG=-ggdb
OPT = -O3
WARN = -Wall
STDCXX = -std=c++11

CPPFLAGS += $(INCPATHS)
CXXFLAGS += $(OPT) $(WARN) $(DEBUG) $(STDCXX)
LDLIBS += $(LIBPATHS) -lreadline -lhistory

.PHONY:	all clean dist

all: $(step0A)

dist: mal

mal: stepA_mal
	cp $< $@

.deps: *.cpp *.h
	$(CXX) $(CXXFLAGS) $(CPPFLAGS) -MM *.cpp > .deps

$(step0A): ReadLine.o String.o
$(step1A): Reader.o Types.o Validation.o
$(step3A): Environment.o
$(step4A): Core.o

clean:
	rm -f *.o $(step0A) .deps mal

-include .deps
