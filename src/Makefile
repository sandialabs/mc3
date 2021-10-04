.PHONY: list all clean

include ../raco.mk

MODULES_RKT := $(call find-rkt,.)
MODULES_ZO := $(call rkt->zo,$(MODULES_RKT))
COMPILED_DIRS := $(call rkt->compiled,$(MODULES_RKT))

list:
	@echo $(COMPILED_DIRS)
	@echo $(MODULES_ZO)

all: $(MODULES_ZO)

clean:
	rm -rf $(COMPILED_DIRS)
