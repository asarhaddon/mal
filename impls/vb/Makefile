include ../../steps.mk

#####################

DEBUG =

SOURCES_BASE = readline.vb types.vb reader.vb printer.vb
SOURCES_LISP = env.vb core.vb

#####################

LIB_CS_SRCS = getline.cs
LIB_VB_SRCS = $(SOURCES_BASE) $(SOURCES_LISP)

FLAGS = $(if $(strip $(DEBUG)),-debug:full,)

#####################

all: $(step0A:=.exe)

dist: mal.exe

mal.exe: $(stepA).exe
	cp $< $@

mal_cs.dll: $(LIB_CS_SRCS)
	mcs $(FLAGS) -target:library $+ -out:$@

mal_vb.dll: mal_cs.dll $(LIB_VB_SRCS)
	vbnc $(FLAGS) -target:library -r:mal_cs.dll $(LIB_VB_SRCS) -out:$@

%.exe: %.vb mal_vb.dll
	vbnc $(FLAGS) -r:mal_vb.dll -r:mal_cs.dll $<

clean:
	rm -f *.dll *.exe *.mdb
