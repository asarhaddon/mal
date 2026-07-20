include ../../steps.mk

OTHER_SRCS = src/Readline.js src/Readline.purs src/Types.purs src/Reader.purs \
             src/Printer.purs src/Env.purs src/Core.purs

all: $(step0A:=.js)

$(step0A:=.js): s%.js: src/s%.purs $(OTHER_SRCS) node_modules/readline-sync
	spago bundle-app --main Mal.S$(firstword $(subst _, ,$*)) --to $@

node_modules/readline-sync:
	npm install

clean:
	rm -rf $(step0A:=.js) output/*
