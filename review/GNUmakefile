TOP := ..
TEXUTIL := $(TOP)/tex-util
TEXINPUTS := .:$(TEXUTIL):

compile := env TEXINPUTS=$(TEXINPUTS) latexmk -g -xelatex -pdf -output-directory=. -aux-directory=.tex-out --halt-on-error -file-line-error -shell-escape

.PHONY: all

.PHONY: nr


all: full 

full: full-paper.tex
	$(compile) full-paper.tex

nr:
	env TEXINPUTS=$(TEXINPUTS) xelatex full-paper


%.pdf : %.tex
	$(compile) $^

.PHONY: clean

clean: 
	rm -rf *.pdf .tex-out
