TOP := ..

BUILD=$(TOP)/build
BIN=$(TOP)/bin

BASES=main impossible
MLBS=$(BASES:%=%.mlb)
CMS=$(BASES:%=%.cm)
SRCS=$(shell echo *.sml)
DML_SRCS=dml/example-dml.sml Unit.sml
DML_CM=dml.cm

MAINS=vml.opt vml vml-test dml-test

.PHONY: mosml

mosml: $(BIN)/vml-test
	@: do nothing, and say nothing about doing nothing

.PHONY: clean

clean:
	rm -f *.ui *.uo
	rm -f $(BIN)/vml $(BIN)/vml.opt $(BIN)/vml-test $(BIN)/dml-test

.PHONY: all

all: $(MAINS:%=$(BIN)/%)
	@: do nothing, and say nothing about doing nothing

.PHONY: mlton

mlton: $(BIN)/vml.opt
	@: do nothing, and say nothing about doing nothing

$(BIN)/vml.opt: $(MLBS) $(SRCS)
	mlton -output $@ -verbose 1 main.mlb

%.mlb: %.cm
	cm2mlb $^ > $@ || rm -f $@

$(BIN)/vml-test: $(SRCS) $(CMS)
	$(TOP)/bin/mosml-compile-cm -o $@ main.cm

$(BIN)/vml: $(SRCS) $(CMS)
	$(TOP)/bin/mosml-compile-cm -o $@ main.cm

dml-test: $(BIN)/dml-test
	@: do nothing, and say nothing about doing nothing

$(BIN)/dml-test: $(DML_SRCS) $(DML_CM)
	$(TOP)/bin/mosml-compile-cm -o $@ $(DML_CM)

millet.cm: $(CMS)
	expand-cm main.cm > $@
