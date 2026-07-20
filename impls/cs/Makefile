include ../../steps.mk

#####################

DEBUG =

SOURCES_BASE = readline.cs types.cs reader.cs printer.cs
SOURCES_LISP = env.cs core.cs stepA_mal.cs
SOURCES = $(SOURCES_BASE) $(SOURCES_LISP)

OTHER_SOURCES = getline.cs

#####################

LIB_SRCS = $(filter-out step%,$(OTHER_SOURCES) $(SOURCES))

FLAGS = $(if $(strip $(DEBUG)),-debug+,)

#####################

all: $(step0A:=.exe)

dist: mal.exe mal

mal.exe: $(stepA).exe
	cp $< $@

# NOTE/WARNING: static linking triggers mono libraries LGPL
# distribution requirements.
# http://www.mono-project.com/archived/guiderunning_mono_applications/
mal: $(stepA).exe mal.dll
	mkbundle --static -o $@ $+ --deps

mal.dll: $(LIB_SRCS)
	mcs $(FLAGS) -target:library $+ -out:$@

$(step0A:=.exe): %.exe: %.cs mal.dll
	mcs $(FLAGS) -r:mal.dll $<

clean:
	rm -f mal *.dll *.exe *.mdb
