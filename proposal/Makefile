
TEX:=proposal.tex
DEPS:=proposal.bib
PDFS:=$(TEX:%.tex=%.pdf)

all: $(PDFS)

proposal.pdf:proposal.tex $(DEPS)
	latexmk -xelatex proposal.tex

clean:
	rm -f *.log *.aux *.toc *.out
	rm -f *.bbl *.blg *.fls *.xml
	rm -f $(PDFS)
