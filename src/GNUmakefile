TOP := ..

BUILD=$(TOP)/build
BIN=$(TOP)/bin

BASES=all vminus pplus
MLBS=$(BASES:%=%.mlb)
CMS=$(BASES:%=%.cm)
SRCS=$(shell echo *.sml)
DML_SRCS=dml/example-dml.sml Unit.sml
DML_CM=dml/dml.cm

MAINS=dtran.opt dtran vminus.opt vminus pplus.opt pplus

RAWTARGETS=$(addprefix $(BIN)/,$(MAINS:%=%))

.PHONY: mosml

mosml: $(BIN)/dtran
	@: do nothing, and say nothing about doing nothing

vminus: $(BIN)/vminus
	@: do nothing, and say nothing about doing nothing

pplus: $(BIN)/pplus
	@: do nothing, and say nothing about doing nothing


.PHONY: clean

clean:
	rm -f *.ui *.uo
	rm -f $(RAWTARGETS)

.PHONY: all

all: $(MAINS:%=$(BIN)/%)
	@: do nothing, and say nothing about doing nothing

.PHONY: mlton

mlton: $(BIN)/dtran.opt
	@: do nothing, and say nothing about doing nothing

vminus-mlton: $(BIN)/vminus.opt
	@: do nothing, and say nothing about doing nothing

pplus-mlton: $(BIN)/pplus.opt
	@: do nothing, and say nothing about doing nothing


$(BIN)/dtran.opt: $(MLBS) $(SRCS)
	mlton -default-ann 'allowExtendedTextConsts true' -output $@ -verbose 1 all.mlb

$(BIN)/vminus.opt: $(MLBS) $(SRCS)
	mlton -default-ann 'allowExtendedTextConsts true' -output $@ -verbose 1 vminus.mlb

$(BIN)/pplus.opt: $(MLBS) $(SRCS)
	mlton -default-ann 'allowExtendedTextConsts true' -output $@ -verbose 1 pplus.mlb


%.mlb: %.cm
	cm2mlb $^ > $@ || rm -f $@

$(BIN)/dtran: $(SRCS) $(CMS)
	$(TOP)/bin/mosml-compile-cm -o $@ all.cm

$(BIN)/vminus: $(SRCS) $(CMS)
	$(TOP)/bin/mosml-compile-cm -o $@ vminus.cm

$(BIN)/pplus: $(SRCS) $(CMS)
	$(TOP)/bin/mosml-compile-cm -o $@ pplus.cm

dml-test: $(BIN)/dml-test
	@: do nothing, and say nothing about doing nothing

$(BIN)/dml-test: $(DML_SRCS) $(DML_CM)
	$(TOP)/bin/mosml-compile-cm -o $@ $(DML_CM)

millet.cm: $(CMS)
	expand-cm all.cm > $@
