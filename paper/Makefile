
TEX:=paper.tex presentation.tex
DEPS:=abstract.tex introduction.tex background.tex formalisation.tex\
futurework.tex conclusion.tex acknowledgements.tex macros.tex cp.tex\
principalcp.tex ccoutput.tex extract.tex gv.tex papercut.tex wft.tex\
gv-trans-types.tex letscompare.tex gv-cps-cp.tex\
gv-types-terms.tex cp-types-terms.tex with-connect-rule.tex focus-rule.tex\
propmacros.tex session-types.tex paper.bib
PDFS:=$(TEX:%.tex=%.pdf)

all: $(PDFS)

paper.pdf:paper.tex $(DEPS)
	latexmk -pdf paper.tex

presentation.pdf:presentation.tex $(DEPS)
	latexmk -pdf presentation.tex

clean:
	rm -f *.log *.aux *.toc *.out
	rm -f *.bbl *.blg *.fls *.xml
	rm -f $(PDFS)
