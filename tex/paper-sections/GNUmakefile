ALL=paper 
TEXINPUTS=.::../../script-util

.PHONY: all

all: full.tex
	env TEXINPUTS=$(TEXINPUTS) latexmk -g -xelatex -pdf -output-directory=. -aux-directory=tex-out --halt-on-error -file-line-error -shell-escape $^
