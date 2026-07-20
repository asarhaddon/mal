include ../../steps.mk

ifneq ($(shell which xcrun),)
	SWIFT = xcrun -sdk macosx swiftc
else
	SWIFT = swiftc
endif

all: $(step0A)

dist: mal

mal: stepA_mal
	cp $< $@

$(step1A): Sources/types.swift Sources/reader.swift Sources/printer.swift Sources/env.swift
$(step4A): Sources/core.swift

$(step0A): %: Sources/%/main.swift
	$(SWIFT) $+ -o $@

clean:
	rm -f $(step0A) mal

