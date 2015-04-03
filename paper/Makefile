
TEX:=paper.tex
PROPDEPS:=with-connect-rule.tex focus-rule.tex propmacros.tex\
session-types.tex
DEPS:=abstract.tex introduction.tex background.tex formalisation.tex\
futurework.tex conclusion.tex acknowledgements.tex macros.tex cp.tex\
principalcp.tex commconvonecp.tex commconvtwocp.tex gv.tex paper.bib
PROPDEPS:=$(PROPDEPS:%.tex=../proposal/%.tex)
PDFS:=$(TEX:%.tex=%.pdf)

all: $(PDFS)

paper.pdf:paper.tex $(DEPS) $(PROPDEPS)
	latexmk -pdf paper.tex

clean:
	rm -f *.log *.aux *.toc *.out
	rm -f *.bbl *.blg *.fls *.xml
	rm -f $(PDFS)
