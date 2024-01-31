ALL=paper 

all: full.tex
	latexmk -xelatex -pdf -output-directory=. -aux-directory=tex-out --halt-on-error -file-line-error -shell-escape $^
