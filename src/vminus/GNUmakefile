TOP := ../..

BUILD=$(TOP)/build
BIN=$(TOP)/bin

BASES=all
MLBS=$(BASES:%=%.mlb)
CMS=$(BASES:%=%.cm)
SRCS=$(shell echo *.sml)

MAINS=vminus

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
	mlton -default-ann 'allowExtendedTextConsts true' -output $@ -verbose 1 all.mlb

%.mlb: %.cm
	cm2mlb $^ > $@ || rm -f $@

$(BIN)/vminus: $(SRCS) $(CMS)
	$(TOP)/bin/mosml-compile-cm -o $@ all.cm

dml-test: $(BIN)/dml-test
	@: do nothing, and say nothing about doing nothing

$(BIN)/dml-test: $(DML_SRCS) $(DML_CM)
	$(TOP)/bin/mosml-compile-cm -o $@ $(DML_CM)

millet.cm: $(CMS)
	expand-cm all.cm > $@
