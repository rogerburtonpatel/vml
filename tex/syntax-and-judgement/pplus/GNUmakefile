ALL := paper 
TOP := ../../..
TEXUTIL := $(TOP)/tex-util
TEXINPUTS := .:$(TEXUTIL):

compile := env TEXINPUTS=$(TEXINPUTS) latexmk -g -xelatex -pdf -output-directory=. -aux-directory=.tex-out --halt-on-error -file-line-error -shell-escape

.PHONY: all

all: syntax-judgement-pplus.tex
	$(compile) $^

%.pdf : %.tex
	$(compile) $^
