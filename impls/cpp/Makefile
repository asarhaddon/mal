include ../../steps.mk

uname_S := $(shell sh -c 'uname -s 2>/dev/null || echo not')

CXX=g++
ifeq ($(uname_S),Darwin)
	# Native build on yosemite. Requires: brew install readline
	READLINE=/usr/local/opt/readline
	INCPATHS=-I$(READLINE)/include
	LIBPATHS=-L$(READLINE)/lib
endif

LD=$(CXX)
AR=ar

DEBUG=-ggdb
CXXFLAGS=-O3 -Wall $(DEBUG) $(INCPATHS) -std=c++11
LDFLAGS=-O3 $(DEBUG) $(LIBPATHS) -L. -lreadline -lhistory

LIBSOURCES=Core.cpp Environment.cpp Reader.cpp ReadLine.cpp String.cpp \
			Types.cpp Validation.cpp
LIBOBJS=$(LIBSOURCES:%.cpp=%.o)

.PHONY:	all clean

.SUFFIXES: .cpp .o

all: $(step0A)

dist: mal

mal: stepA_mal
	cp $< $@

.deps: *.cpp *.h
	$(CXX) $(CXXFLAGS) -MM *.cpp > .deps

$(step0A): %: %.o libmal.a
	$(LD) $^ -o $@ $(LDFLAGS)

libmal.a: $(LIBOBJS)
	$(AR) rcs $@ $^

.cpp.o:
	$(CXX) $(CXXFLAGS) -c $< -o $@

clean:
	rm -rf *.o $(step0A) libmal.a .deps mal

-include .deps
