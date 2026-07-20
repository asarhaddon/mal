include ../../steps.mk

BINS = reader.js printer.js env.js core.js utils.js $(step0A:=.js)

LSC = lsc

all: node_modules $(BINS)

node_modules:
	npm install

$(BINS): %.js: %.ls node_modules
	$(LSC) -d -c $<

$(step1A:=.js): utils.js reader.js printer.js
$(step3A:=.js): env.js
$(step4A:=.js): core.js

clean:
	rm -f $(BINS)
