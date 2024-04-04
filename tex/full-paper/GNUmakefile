TOP := ../..
TEXUTIL := $(TOP)/tex-util
TEXINPUTS := .:$(TEXUTIL):

compile := env TEXINPUTS=$(TEXINPUTS) latexmk -g -xelatex -pdf -output-directory=. -aux-directory=tex-out --halt-on-error -file-line-error -shell-escape

.PHONY: all


# builds the full paper from the outline
all: build_with_section_numbers build_full

build_with_section_numbers: full-paper-with-outline.tex
	$(compile) $^

build_full: full-paper-with-outline.tex
	$(shell sed -E 's#\\[0-9](.*$$)##g' full-paper-with-outline.tex > full-paper.tex)
	$(compile) full-paper.tex

outline: full-outline.pdf
	@: go

%.pdf : %.tex
	$(compile) $^
