TOP := ..

BUILD=$(TOP)/build
BIN=$(TOP)/bin

BASES=main impossible
MLBS=$(BASES:%=%.mlb)
CMS=$(BASES:%=%.cm)
SRCS=$(shell echo *.sml)

MAINS=vml.opt vml vml-test

.PHONY: mosml

mosml: $(BIN)/vml-test
	@: do nothing, and say nothing about doing nothing

# mosml: $(BIN)/vml
# 	@: do nothing, and say nothing about doing nothing

.PHONY: clean

clean:
	rm -f *.ui *.uo
	rm -f $(BIN)/vml $(BIN)/vml.opt $(BIN)/vml-test

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

millet.cm: $(CMS)
	expand-cm main.cm > $@
