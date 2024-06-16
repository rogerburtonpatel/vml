TOP := ..

BUILD=$(TOP)/build
BIN=$(TOP)/bin

BASES=all vminus pplus
MLBS=$(BASES:%=%.mlb)
CMS=$(BASES:%=%.cm)
SRCS=$(shell echo *.sml)
DML_SRCS=dml/example-dml.sml Unit.sml
DML_CM=dml/dml.cm

MAINS= dtran vminus pplus

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

.PHONY: dtran-mlton vminus-mlton pplus-mlton

dtran-mlton: $(MLBS) $(SRCS)
	mlton -default-ann 'allowExtendedTextConsts true' -output dtran -verbose 1 all.mlb

vminus-mlton: $(MLBS) $(SRCS)
	mlton -default-ann 'allowExtendedTextConsts true' -output vminus -verbose 1 vminus.mlb

pplus-mlton: $(MLBS) $(SRCS)
	mlton -default-ann 'allowExtendedTextConsts true' -output pplus -verbose 1 pplus.mlb


# $(BIN)/dtran.opt: $(MLBS) $(SRCS)
# 	mlton -default-ann 'allowExtendedTextConsts true' -output $@ -verbose 1 all.mlb

# $(BIN)/vminus.opt: $(MLBS) $(SRCS)
# 	mlton -default-ann 'allowExtendedTextConsts true' -output $@ -verbose 1 vminus.mlb

# $(BIN)/pplus.opt: $(MLBS) $(SRCS)
# 	mlton -default-ann 'allowExtendedTextConsts true' -output $@ -verbose 1 pplus.mlb


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
