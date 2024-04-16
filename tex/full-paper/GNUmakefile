TOP := ../..
TEXUTIL := $(TOP)/tex-util
TEXINPUTS := .:$(TEXUTIL):

compile := env TEXINPUTS=$(TEXINPUTS) latexmk -g -xelatex -pdf -output-directory=. -aux-directory=.tex-out --halt-on-error -file-line-error -shell-escape

.PHONY: all


# builds the full paper from the outline
all: full 

# with_outline_bullets: outline.pdf
# 	@: go

full: outline.tex
	$(shell sed -E 's#(\\[0-9](.*$$)|\\begin{outline}.*$$|\\end{outline}.*$$)##g' outline.tex > full-paper.tex)
	$(compile) full-paper.tex

outline: outline.pdf
	@: go

%.pdf : %.tex
	$(compile) $^

.PHONY: clean

clean: 
	rm -rf *.pdf .tex-out
