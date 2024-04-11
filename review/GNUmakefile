TOP := ..
TEXUTIL := $(TOP)/tex-util
TEXINPUTS := .:$(TEXUTIL):

compile := env TEXINPUTS=$(TEXINPUTS) latexmk -g -xelatex -pdf -output-directory=. -aux-directory=.tex-out --halt-on-error -file-line-error -shell-escape

.PHONY: all


# builds the full paper from the outline
all: section2-4824

section2: section2.pdf
	@: go

section2-4824: section2-4824.pdf
	@: go

%.pdf : %.tex
	$(compile) $^
