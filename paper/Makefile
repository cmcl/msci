
TEX:=paper.tex
DEPS:=abstract.tex introduction.tex background.tex formalisation.tex\
futurework.tex conclusion.tex acknowledgements.tex macros.tex cp.tex\
principalcp.tex ccoutput.tex extract.tex gv.tex papercut.tex\
gv-types-terms.tex cp-types-terms.tex with-connect-rule.tex focus-rule.tex\
propmacros.tex session-types.tex paper.bib
PDFS:=$(TEX:%.tex=%.pdf)

all: $(PDFS)

paper.pdf:paper.tex $(DEPS) $(PROPDEPS)
	latexmk -pdf paper.tex

clean:
	rm -f *.log *.aux *.toc *.out
	rm -f *.bbl *.blg *.fls *.xml
	rm -f $(PDFS)
