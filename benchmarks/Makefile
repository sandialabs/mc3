.PHONY: all all-live all-single repeat all-nusmv summarize compare clean clean-nusmv

include ../raco.mk

MC3_RKT := ../src/mc3.rkt
MC3_ARGS := --time --backward --random-seed 0 --verbosity 2
DEPS_RKT := $(call find-rkt,../src)

all: all-live all-single

HWMCC15_LIVE_AIGS := $(sort $(wildcard hwmcc15-benchmarks/live/*.aig))
HWMCC15_LIVE_LOGS := $(patsubst %.aig,%.log,$(HWMCC15_LIVE_AIGS))
all-live: $(HWMCC15_LIVE_LOGS)

HWMCC15_SINGLE_AIGS := $(sort $(wildcard hwmcc15-benchmarks/single/*.aig))
HWMCC15_SINGLE_LOGS := $(patsubst %.aig,%.log,$(HWMCC15_SINGLE_AIGS))
all-single: $(HWMCC15_SINGLE_LOGS)

HWMCC15_COMPLETED := $(shell grep -l 'INFO: solution:' -r hwmcc15-benchmarks/)
repeat: $(HWMCC15_COMPLETED)

HWMCC15_SMV_LOGS_00 := $(patsubst %.log,%.smvlog00,$(HWMCC15_COMPLETED))
HWMCC15_SMV_LOGS_01 := $(patsubst %.log,%.smvlog01,$(HWMCC15_COMPLETED))
HWMCC15_SMV_LOGS_10 := $(patsubst %.log,%.smvlog10,$(HWMCC15_COMPLETED))
HWMCC15_SMV_LOGS_11 := $(patsubst %.log,%.smvlog11,$(HWMCC15_COMPLETED))
HWMCC15_SMV_LOGS := $(HWMCC15_SMV_LOGS_00) $(HWMCC15_SMV_LOGS_01) $(HWMCC15_SMV_LOGS_10) $(HWMCC15_SMV_LOGS_11)
all-nusmv: $(HWMCC15_SMV_LOGS)
clean-nusmv:
	rm -f $(HWMCC15_SMV_LOGS)

TIMEOUT := 300s
MEMOUT := 1073741824 # 1 GiB, i.e., 1024^3 bytes, i.e., 2^30 bytes
%.log : %.aig $(MC3_RKT) $(DEPS_RKT)
	timeout --foreground --signal=9 $(TIMEOUT) prlimit --as=$(MEMOUT) racket $(MC3_RKT) $(MC3_ARGS) $< > $(patsubst %.aig,%.log,$<) 2>&1
%.smvlog00: %.aig
	aigtosmv -b $< | timeout --foreground --signal=9 $(TIMEOUT) prlimit --as=$(MEMOUT) NuSMV -v 2 -dcx /dev/stdin > $@ 2>&1
%.smvlog01: %.aig
	aigtosmv -b $< | timeout --foreground --signal=9 $(TIMEOUT) prlimit --as=$(MEMOUT) NuSMV -v 2 -dcx -df /dev/stdin > $@ 2>&1
%.smvlog10: %.aig
	aigtosmv -b $< | timeout --foreground --signal=9 $(TIMEOUT) prlimit --as=$(MEMOUT) NuSMV -v 2 -dcx -dynamic /dev/stdin > $@ 2>&1
%.smvlog11: %.aig
	aigtosmv -b $< | timeout --foreground --signal=9 $(TIMEOUT) prlimit --as=$(MEMOUT) NuSMV -v 2 -dcx -dynamic -df /dev/stdin > $@ 2>&1

summarize:
	grep 'INFO: solution:' -r hwmcc15-benchmarks/ | sort > summary.txt

compare:
	@racket collect-results.rkt -- $(patsubst %.log,%,$(HWMCC15_COMPLETED)) > comparison.tex

clean: clean-nusmv
	rm -f $(HWMCC15_LIVE_LOGS) $(HWMCC15_SINGLE_LOGS) summary.txt comparison.tex
