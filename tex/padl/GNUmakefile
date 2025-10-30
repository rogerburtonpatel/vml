TOP := ../..
TEXUTIL := $(TOP)/tex-util
TEXINPUTS := .:$(TEXUTIL):

TEXOPTS := -output-directory=. -aux-directory=.tex-out --halt-on-error -file-line-error -shell-escape

compile := env TEXINPUTS=$(TEXINPUTS) latexmk --norc -r ./latexmkrc -pdf -xelatex $(TEXOPTS)

.PHONY: all padl draft


# builds the full paper
all: padl 

# $(shell sed -E 's#(\\[0-9](.*$$)|\\begin{outline}.*$$|\\end{outline}.*$$)##g' body.tex > full-paper.tex)

# public: Thesis.pdf
# 	@echo "cp Thesis.pdf $$DIRWEBSITE/assets"
# 	$(shell cp Thesis.pdf $$DIRWEBSITE/assets)

# Thesis.pdf: 
# 	$(shell cp fullpaper.pdf Thesis.pdf)

draft:
	env TEXINPUTS=$(TEXINPUTS) xelatex $(TEXOPTS) --output-directory .tex-out padl-final.tex
	cp -u .tex-out/padl-final.pdf .

padl: padl-final.pdf
	@ : go 

%.pdf : %.tex
	$(compile) $^

.PHONY: clean

clean: 
	rm -rf *.pdf .tex-out
