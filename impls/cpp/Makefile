uname_S != uname -s 2>/dev/null

CXX=g++
ifeq ($(uname_S),Darwin)
	# Native build on yosemite. Requires: brew install readline
	READLINE=/usr/local/opt/readline
	INCPATHS=-I$(READLINE)/include
	LIBPATHS=-L$(READLINE)/lib
endif

LINK.o = $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(LDFLAGS)
AR=ar

DEBUG=-ggdb
OPT = -O3
WARN = -Wall
STDCXX = -std=c++11

CPPFLAGS += $(INCPATHS)
CXXFLAGS += $(OPT) $(WARN) $(DEBUG) $(STDCXX)
LDLIBS += $(LIBPATHS) -lreadline -lhistory

LIBSOURCES=Core.cpp Environment.cpp Reader.cpp ReadLine.cpp String.cpp \
			Types.cpp Validation.cpp
LIBOBJS=$(LIBSOURCES:%.cpp=%.o)

MAINS=$(wildcard step*.cpp)
TARGETS=$(MAINS:%.cpp=%)

.PHONY:	all clean dist

all: $(TARGETS)

dist: mal

mal: stepA_mal
	cp $< $@

.deps: *.cpp *.h
	$(CXX) $(CXXFLAGS) $(CPPFLAGS) -MM *.cpp > .deps

$(TARGETS): libmal.a

libmal.a: $(LIBOBJS)
	$(AR) rcs $@ $^

clean:
	rm -f *.o $(TARGETS) libmal.a .deps mal

-include .deps
