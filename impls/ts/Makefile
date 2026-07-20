include ../../steps.mk

all: ts

node_modules:
	npm install

$(step0A:=.js): %.js: node_modules types.ts reader.ts printer.ts env.ts core.ts %.ts
	./node_modules/.bin/tsc -p ./


.PHONY: ts clean

ts: $(step0A:=.js)

clean:
	rm -f *.js
