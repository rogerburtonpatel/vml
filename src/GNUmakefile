TOP := ..

BUILD=$(TOP)/build
BIN=$(TOP)/bin

BASES=all
MLBS=$(BASES:%=%.mlb)
CMS=$(BASES:%=%.cm)
SRCS=$(shell echo *.sml)
DML_SRCS=dml/example-dml.sml Unit.sml
DML_CM=dml.cm

MAINS=dtran.opt dtran

.PHONY: mosml

mosml: $(BIN)/dtran
	@: do nothing, and say nothing about doing nothing

.PHONY: clean

clean:
	rm -f *.ui *.uo
	rm -f $(BIN)/dtran $(BIN)/dtran.opt

.PHONY: all

all: $(MAINS:%=$(BIN)/%)
	@: do nothing, and say nothing about doing nothing

.PHONY: mlton

mlton: $(BIN)/dtran.opt
	@: do nothing, and say nothing about doing nothing

$(BIN)/dtran.opt: $(MLBS) $(SRCS)
	mlton -default-ann 'allowExtendedTextConsts true' -output $@ -verbose 1 all.mlb

%.mlb: %.cm
	cm2mlb $^ > $@ || rm -f $@

$(BIN)/dtran: $(SRCS) $(CMS)
	$(TOP)/bin/mosml-compile-cm -o $@ all.cm

dml-test: $(BIN)/dml-test
	@: do nothing, and say nothing about doing nothing

$(BIN)/dml-test: $(DML_SRCS) $(DML_CM)
	$(TOP)/bin/mosml-compile-cm -o $@ $(DML_CM)

millet.cm: $(CMS)
	expand-cm all.cm > $@
