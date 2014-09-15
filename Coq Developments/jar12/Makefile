############################################################################
#
#  Primary targets:
#    all           - the default target; synonym for 'coq'
#    coq           - builds all .vo files
#    doc           - synonym for 'documentation'
#    documentation - builds all html documentation
#    clean         - removes generated files
#
############################################################################

include Makefile.include

## Directory where generated HTML documentation should go.

DOCDIR = html
DOCDIRTWO = html2

## List of files to be compiled and documented.

FSUBFILES= \
	Fnamed.v Fnamedcofinite.v Fnamedcontext.v Fnamedcontextcofinite.v \
	Fnameless.v Fnamelesscofinite.v \
	Fequiv.v
FLINFILES = Flinear.v

FSUBFILES_VO=$(FSUBFILES:.v=.vo)
FLINFILES_VO=$(FLINFILES:.v=.vo)

## Include directories

INCFLAGS = -I . -I lib
$(FLINFILES_VO):INCFLAGS += -I metatheory


############################################################################

.PHONY: all clean coq flin fsub doc documentation 
.SUFFIXES: .v .vo

all:
	+make coq

coq: fsub flin

fsub: $(FSUBFILES_VO)

flin:: 
	cd metatheory; $(MAKE) all
flin:: $(FLINFILES_VO)

doc:
	make documentation

documentation: $(DOCDIR) $(DOCDIRTWO) coq
	$(COQDOC) --quiet --noindex --html -d $(DOCDIR) $(FSUBFILES) $(FLINFILES)
	$(COQDOC) -l --quiet --noindex --html -d $(DOCDIRTWO) $(FSUBFILES) $(FLINFILES)

clean:
	rm -f *.vo *.glob *.cmi *.cmx *.o 
	rm -f lib/*.vo lib/*.glob
	cd metatheory; $(MAKE) clean
	rm -rf $(DOCDIR)/* 
	rm -rf $(DOCDIRTWO)/* 

############################################################################

%.vo: %.v Makefile
	$(COQC) -q $(INCFLAGS) $<

$(DOCDIR):
	mkdir -p $(DOCDIR)

$(DOCDIRTWO):
	mkdir -p $(DOCDIRTWO)

############################################################################

.depend: $(FSUBFILES) $(FLINFILES) Makefile
	$(COQDEP) $(INCFLAGS) $(FSUBFILES) > .depend
	$(COQDEP) $(INCFLAGS) -I metatheory $(FLINFILES) >> .depend

include .depend
