MAIN = draft

all : $(MAIN).pdf

$(MAIN).pdf : $(wildcard *.tex)
	pdflatex $(MAIN).tex
	bibtex $(MAIN)
	pdflatex $(MAIN).tex

.PHONY : $(MAIN).pdf
