include ../../steps.mk

EXEC_DIR := target/release

all: $(step0A:%=$(EXEC_DIR)/%)

$(step0A:%=$(EXEC_DIR)/%): $(EXEC_DIR)/%: %.rs
	cargo build --release --bin $*

$(step0A:%=$(EXEC_DIR)/%): readline.rs
$(step1A:%=$(EXEC_DIR)/%): types.rs reader.rs printer.rs
$(step3A:%=$(EXEC_DIR)/%): env.rs
$(step4A:%=$(EXEC_DIR)/%): core.rs

lint:
	rustfmt *.rs
	cargo clippy

.PHONY: clean lint all

clean:
	rm -fr target/
	rm -f .mal-history *~ Cargo.lock
