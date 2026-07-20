# Helper for impls/quux/Makefile

# The following example assumes that
#  * the implementation language is compiled and linked in two steps
#  * the source files carry the `.qx` extension
#  * the quux_STEP_TO_PROG macro maps % to obj/%,
#  * only steps 0-2 are implemented (`all` only builds these steps).

# include ../../steps.mk

# deps1A := obj/printer.o obj/reader.o
# deps3A := obj/env.o
# deps4A := obj/core.o

# .PHONY: all
# all: $(step02:%=obj/%)

# $(step1A:%=obj/%): $(deps1A)
# $(step3A:%=obj/%): $(deps3A)
# $(step4A:%=obj/%): $(deps4A)
# $(step0A:%=obj/%): obj/%: obj/%.o
# 	LINK -o $@ $^

# $(step0A:%=obj/%.o) $(deps1A) $(deps3A) $(deps4A): obj/%.o: %.qx | obj
# 	COMPILE -o $@ $<

# obj:
# 	mkdir obj

# .PHONY: clean
# clean:
# 	rm -fr obj

step0 := step0_repl
step1 := step1_read_print
step2 := step2_eval
step3 := step3_env
step4 := step4_if_fn_do
step5 := step5_tco
step6 := step6_file
step7 := step7_quote
step8 := step8_macros
step9 := step9_try
stepA := stepA_mal

# Set `step5:=` if you want to remove it from the following ranges.

step01 = $(step0) $(step1)
step02 = $(step0) $(step1) $(step2)
step03 = $(step0) $(step1) $(step2) $(step3)
step04 = $(step0) $(step1) $(step2) $(step3) $(step4)
step05 = $(step0) $(step1) $(step2) $(step3) $(step4) $(step5)
step06 = $(step0) $(step1) $(step2) $(step3) $(step4) $(step5) $(step6)
step07 = $(step0) $(step1) $(step2) $(step3) $(step4) $(step5) $(step6) $(step7)
step08 = $(step0) $(step1) $(step2) $(step3) $(step4) $(step5) $(step6) $(step7) $(step8)
step09 = $(step0) $(step1) $(step2) $(step3) $(step4) $(step5) $(step6) $(step7) $(step8) $(step9)
step0A = $(step0) $(step1) $(step2) $(step3) $(step4) $(step5) $(step6) $(step7) $(step8) $(step9) $(stepA)
step1A =          $(step1) $(step2) $(step3) $(step4) $(step5) $(step6) $(step7) $(step8) $(step9) $(stepA)
step2A =                   $(step2) $(step3) $(step4) $(step5) $(step6) $(step7) $(step8) $(step9) $(stepA)
step3A =                            $(step3) $(step4) $(step5) $(step6) $(step7) $(step8) $(step9) $(stepA)
step4A =                                     $(step4) $(step5) $(step6) $(step7) $(step8) $(step9) $(stepA)
step5A =                                              $(step5) $(step6) $(step7) $(step8) $(step9) $(stepA)
step6A =                                                       $(step6) $(step7) $(step8) $(step9) $(stepA)
step7A =                                                                $(step7) $(step8) $(step9) $(stepA)
step8A =                                                                         $(step8) $(step9) $(stepA)
step9A =                                                                                  $(step9) $(stepA)
