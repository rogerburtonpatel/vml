TOP := ../..
TEXUTIL := $(TOP)/tex-util
TEXINPUTS := .:$(TEXUTIL):

compile := env TEXINPUTS=$(TEXINPUTS) latexmk -g -xelatex -pdf -output-directory=. -aux-directory=tex-out --halt-on-error -file-line-error -shell-escape

.PHONY: all

all: full-paper.tex
	$(compile) $^

outline: full-outline.pdf
	@: go

%.pdf : %.tex
	$(compile) $^
