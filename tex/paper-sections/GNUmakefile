ALL=paper 
TEXINPUTS=.:../../tex-util:

compile := env TEXINPUTS=$(TEXINPUTS) latexmk -g -xelatex -pdf -output-directory=. -aux-directory=tex-out --halt-on-error -file-line-error -shell-escape

.PHONY: all

all: full.tex
	$(compile) $^

%.pdf : %.tex
	$(compile) $^
