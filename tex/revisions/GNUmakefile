TOP := ../..
TEXUTIL := $(TOP)/tex-util
TEXINPUTS := .:$(TEXUTIL):

compile := env TEXINPUTS=$(TEXINPUTS) latexmk -g -xelatex -pdf -output-directory=. -aux-directory=.tex-out --halt-on-error -file-line-error -shell-escape

.PHONY: all


# builds the full paper
all: full 

# $(shell sed -E 's#(\\[0-9](.*$$)|\\begin{outline}.*$$|\\end{outline}.*$$)##g' body.tex > full-paper.tex)

full: fullpaper.pdf
	@ : go 

%.pdf : %.tex
	$(compile) $^

.PHONY: clean

clean: 
	rm -rf *.pdf .tex-out
