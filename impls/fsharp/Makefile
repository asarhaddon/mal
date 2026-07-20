include ../../steps.mk

#####################

DEBUG = 

DLL_SOURCES = types.fs error.fs node.fs printer.fs tokenizer.fs reader.fs \
  readline.fs core.fs env.fs

TERMINAL_SOURCES = terminal.cs

#####################

FSFLAGS = $(if $(strip $(DEBUG)),--debug+,--debug- --optimize+ --tailcalls+)
CSFLAGS = $(if $(strip $(DEBUG)),-debug+,)
#####################

all: $(step0A:=.exe)

dist: mal.exe mal

mal.exe: stepA_mal.exe
	cp $< $@

# NOTE/WARNING: static linking triggers mono libraries LGPL
# distribution requirements.
# http://www.mono-project.com/archived/guiderunning_mono_applications/
mal: $(stepA).exe Mono.Terminal.dll mal.dll
	mkbundle --static -o $@ $+ --deps

Mono.Terminal.dll: $(TERMINAL_SOURCES)
	mcs $(CSFLAGS) -target:library $+ -out:$@

mal.dll: $(DLL_SOURCES) Mono.Terminal.dll
	fsharpc $(FSFLAGS) -o $@ -r Mono.Terminal.dll -a $(DLL_SOURCES)

$(step0A:=.exe): %.exe: %.fs mal.dll
	fsharpc $(FSFLAGS) -o $@ -r mal.dll $<

clean:
	rm -f mal *.dll *.exe *.mdb
