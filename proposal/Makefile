
TEX:=proposal.tex
DEPS:=proposal.bib with-connect-rule.tex focus-rule.tex propmacros.tex\
macros.tex
PDFS:=$(TEX:%.tex=%.pdf)

all: $(PDFS)

proposal.pdf:proposal.tex $(DEPS)
	latexmk -pdf proposal.tex

clean:
	rm -f *.log *.aux *.toc *.out
	rm -f *.bbl *.blg *.fls *.xml
	rm -f $(PDFS)
