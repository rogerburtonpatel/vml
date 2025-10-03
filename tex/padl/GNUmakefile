TOP := ../..
TEXUTIL := $(TOP)/tex-util
TEXINPUTS := .:$(TEXUTIL):

compile := env TEXINPUTS=$(TEXINPUTS) latexmk -pdf -xelatex -output-directory=. -aux-directory=.tex-out --halt-on-error -file-line-error -shell-escape

.PHONY: all full public Thesis


# builds the full paper
all: full 

# $(shell sed -E 's#(\\[0-9](.*$$)|\\begin{outline}.*$$|\\end{outline}.*$$)##g' body.tex > full-paper.tex)

public: Thesis.pdf
	@echo "cp Thesis.pdf $$DIRWEBSITE/assets"
	$(shell cp Thesis.pdf $$DIRWEBSITE/assets)

Thesis.pdf: 
	$(shell cp fullpaper.pdf Thesis.pdf)

full: fullpaper.pdf
	@ : go 

%.pdf : %.tex
	$(compile) $^

.PHONY: clean

clean: 
	rm -rf *.pdf .tex-out
