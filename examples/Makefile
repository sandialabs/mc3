.PHONY: list all clean compile

include ../raco.mk

MC3_RKT := ../src/mc3.rkt # also included in `DEPS_RKT`
MC3_ARGS := --totality --verbosity 2 --random-seed 1
DEPS_RKT := $(call find-rkt,../src)
EXAMPLES_RKT := $(wildcard *.rkt)
EXAMPLES_AIG := $(wildcard *.aig)
EXAMPLES_SMV := $(wildcard *.smv)
EXAMPLES_LOG := $(patsubst %.rkt,%.log,$(EXAMPLES_RKT)) $(patsubst %.aig,%.log,$(EXAMPLES_AIG)) $(patsubst %.smv,%.log,$(EXAMPLES_SMV))
EXAMPLES_CSV := $(patsubst %.log,%.csv,$(EXAMPLES_LOG))

ifeq ($(DEBUG),1)
  RACKET_ARGS := -l errortrace -t
else
  RACKET_ARGS :=
endif

list:
	@echo $(EXAMPLES_LOG)

all: $(EXAMPLES_LOG) $(EXAMPLES_CSV)

clean:
	rm -f $(EXAMPLES_LOG) $(EXAMPLES_CSV)
	rm -rf $(call rkt->compiled,$(EXAMPLES_RKT))

define run-mc3 =
racket $(RACKET_ARGS) $(MC3_RKT) $(MC3_ARGS) $< | tee $(patsubst %$(suffix $<),%.log,$<)
endef
%.log %.csv : %.rkt $(MC3_RKT) $(DEPS_RKT)
	$(run-mc3)
%.log %.csv : %.aig $(MC3_RKT) $(DEPS_RKT)
	$(run-mc3)
%.log %.csv : %.smv $(MC3_RKT) $(DEPS_RKT)
	$(run-mc3)


## Extras, not yet worked in with the overall dependency chain or `make all`.
compile: $(call rkt->zo,$(EXAMPLES_RKT))
