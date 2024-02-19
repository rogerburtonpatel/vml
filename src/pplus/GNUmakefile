TOP := ../..

BUILD=$(TOP)/build
BIN=$(TOP)/bin

BASES=main impossible
MLBS=$(BASES:%=%.mlb)
CMS=$(BASES:%=%.cm)
SRCS=$(shell echo *.sml)

MAINS=pplus.opt pplus

.PHONY: mosml

mosml: $(BIN)/pplus
	@: do nothing, and say nothing about doing nothing

.PHONY: clean

clean:
	rm -f *.ui *.uo
	rm -f $(BIN)/pp $(BIN)/pp.opt 

.PHONY: all

all: $(MAINS:%=$(BIN)/%)
	@: do nothing, and say nothing about doing nothing

.PHONY: mlton

mlton: $(BIN)/pp.opt
	@: do nothing, and say nothing about doing nothing

$(BIN)/pp.opt: $(MLBS) $(SRCS)
	mlton -default-ann 'allowExtendedTextConsts true' -output $@ -verbose 1 main.mlb

%.mlb: %.cm
	cm2mlb $^ > $@ || rm -f $@

$(BIN)/pplus: $(SRCS) $(CMS)
	$(TOP)/bin/mosml-compile-cm -o $@ main.cm

millet.cm: $(CMS)
	expand-cm main.cm > $@
