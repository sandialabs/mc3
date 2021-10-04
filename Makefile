.PHONY: list all all-examples all-src clean

list clean:
	$(MAKE) --directory=examples $@
	$(MAKE) --directory=src $@

all: all-examples
all-examples: all-src
	$(MAKE) --directory=examples all
all-src:
	$(MAKE) --directory=src all
