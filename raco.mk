define find-rkt =
$(shell find $(1) -type f -name '*.rkt')
endef

define rkt->compiled =
$(sort $(addsuffix compiled,$(dir $(1))))
endef

## Given a .rkt, return the .zo that `raco make` will produce.
define rkt->zo =
$(foreach rkt,$(1),$(dir $(rkt))compiled/$(patsubst %.rkt,%_rkt.zo,$(notdir $(rkt))))
endef

## Given a .zo, return the .rkt that `raco make` will produce it from.
define zo->rkt =
$(foreach zo,$(1),$(shell realpath --canonicalize-missing $(dir $(zo))../$(subst _rkt,.rkt,$(notdir $(basename $(zo))))))
endef

## Use "Secondary Expansion" for ".../compiled/module_rkt.zo: .../module.rkt".
.SECONDEXPANSION:
%.zo : $$(call zo->rkt,$$@)
	raco make --no-deps $<
