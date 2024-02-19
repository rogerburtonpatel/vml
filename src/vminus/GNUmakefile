TOP := ../..

BUILD=$(TOP)/build
BIN=$(TOP)/bin

BASES=main impossible
MLBS=$(BASES:%=%.mlb)
CMS=$(BASES:%=%.cm)
SRCS=$(shell echo *.sml)

MAINS=vminus.opt vminus

.PHONY: mosml

mosml: $(BIN)/vminus
	@: do nothing, and say nothing about doing nothing

.PHONY: clean

clean:
	rm -f *.ui *.uo
	rm -f $(BIN)/vminus $(BIN)/vminus.opt

.PHONY: all

all: $(MAINS:%=$(BIN)/%)
	@: do nothing, and say nothing about doing nothing

.PHONY: mlton

mlton: $(BIN)/vminus.opt
	@: do nothing, and say nothing about doing nothing

$(BIN)/vminus.opt: $(MLBS) $(SRCS)
	mlton -default-ann 'allowExtendedTextConsts true' -output $@ -verbose 1 main.mlb

%.mlb: %.cm
	cm2mlb $^ > $@ || rm -f $@

$(BIN)/vminus: $(SRCS) $(CMS)
	$(TOP)/bin/mosml-compile-cm -o $@ main.cm

millet.cm: $(CMS)
	expand-cm main.cm > $@
