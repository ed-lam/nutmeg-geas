include ../Makefile.config

#---------------------------------------
# Directories
#---------------------------------------

SRCDIR = $(shell pwd)
#
# Installation directory
#
SITE-LIB = $(shell $(OCAMLFIND) printconf destdir)
PKG-NAME = fzn_phage
SITE-LIB-PKG = $(SITE-LIB)/$(PKG-NAME)

#---------------------------------------
# CAML part
#---------------------------------------

#REQ_PKG = "extlib camlidl"
REQ_PKG = ""

MLMODULES=\
   dynArray \
	 opts \
   util dom token problem \
	 simplify \
	 polarity half_reify \
   registry check \
   lexer parser

OCAMLINC=-I ../ml

OCAMLFLAGS+=$(OCAMLINC)
OCAMLOPTFLAGS+=$(OCAMLINC)

#PROF = -ccopt "-pg"
PROF =

#---------------------------------------
# Rules
#---------------------------------------

# Global rules
#TESTS=testPath testInterpret testLexer
TARGETS=fzn_phage
TARGETS_BYTE=$(TARGETS:%=%.byte)
TARGETS_PROF=$(TARGETS:%=%.p)
TARGETS_DEBUG=$(TARGETS:%=%.debug)

TESTS=$(basename $(wildcard tests/*.ml))
TESTS_BYTE=$(TESTS:%=%.byte)
TESTS_PROF=$(TESTS:%=%.p)
TESTS_DEBUG=$(TESTS:%=%.debug)

#all: opt byte
all: opt

#byte: $(TARGETS_BYTE) $(TESTS_BYTE)
#opt: $(TARGETS) $(TESTS)
#prof: $(TARGETS_PROF) $(TESTS_PROF)
#debug: $(TARGETS_DEBUG) $(TESTS_DEBUG)
byte: $(TARGETS_BYTE)
opt: $(TARGETS)
prof: $(TARGETS_PROF)
debug: $(TARGETS_DEBUG)

#$(TARGETS_BYTE) : %.byte : $(MLMODULES:%=%.cmo) %.ml
#	$(OCAMLFIND) ocamlc $(OCAMLFLAGS) -o $@ $(subst .byte,.mli,$@)  $^ -package $(REQ_PKG) -linkpkg

#libphage_ml.a : ../ml/libphage_ml.a
#	cp ../ml/libphage_ml.a .

$(TARGETS) : phage.a libphage_ml.a
$(TARGETS_DEBUG) : phage.a libphage_ml.a

phage.a: ../ml/phage.a
	cp ../ml/phage.a .
libphage_ml.a: ../ml/libphage_ml.a
	cp ../ml/libphage_ml.a .

$(TARGETS) : % : $(MLMODULES:%=%.cmx) %.ml $(PHAGE_LIB)
	$(OCAMLFIND) ocamlopt $(OCAMLOPTFLAGS) -o $@ \
  -ccopt "-L /opt/local/lib/ocaml" \
  $(PROF) \
  ../ml/phage.cmxa \
  $@.mli $^ -package $(REQ_PKG) -linkpkg

$(TARGETS_DEBUG) : %.debug : $(MLMODULES:%=%.cmo) %.ml
	$(OCAMLFIND) ocamlc $(OCAMLFLAGS) -custom -g -o $@ \
  -ccopt "-L /opt/local/lib/ocaml" \
  ../ml/phage.cma \
  $(subst .debug,.mli,$@)  $^ -package $(REQ_PKG) -linkpkg

$(TARGETS_PROF) : %.p : $(MLMODULES:%=%.p.cmx) %.ml
	$(OCAMLFIND) ocamlopt -p $(OCAMLFLAGS) -o $@ \
  -ccopt "-L /opt/local/lib/ocaml" \
  ../ml/phage.cmxa \
  $(subst .p,.mli,$@) $^ -package $(REQ_PKG) -linkpkg

clobber: clean
	/bin/rm -f Makefile.depend TAGS
	/bin/rm -f $(TARGETS) $(TARGETS_BYTE) $(TARGETS_PROF) $(TARGETS_DEBUG)

clean:
	/bin/rm -f *.cm[ioxat] *.cmti *.o *.cmxa *.annot *.html *.ps *.pdf *.dvi *.out
	/bin/rm -f lexer.ml
	/bin/rm -f *.aux *.bbl *.blg *.dvi *.pdf *.log *.toc *.idx *.ilg *.ind ocamldoc*.tex ocamldoc.sty

wc: $(SRC)
	wc $^

#--------------------------------------------------------------
# IMPLICIT RULES AND DEPENDENCIES
#--------------------------------------------------------------

.SUFFIXES: .ml .mli .cmi .cmo .cmx

#-----------------------------------
# CAML
#-----------------------------------

%.ml: %.mll
	$(OCAMLLEX) $^

%.ml %.mli: %.mly
	$(OCAMLYACC) $^

%.cmi: %.mli
	$(OCAMLFIND) ocamlc $(OCAMLFLAGS) -package $(REQ_PKG) -c $<

%.cmo: %.ml
	$(OCAMLFIND) ocamlc $(OCAMLFLAGS) -package $(REQ_PKG) -c $<

%.cmx: %.ml
	$(OCAMLFIND) ocamlopt $(OCAMLOPTFLAGS) -package $(REQ_PKG) -c $<

%.p.cmx: %.ml
	$(OCAMLFIND) ocamlopt -p $(OCAMLOPTFLAGS) -package $(REQ_PKG) -c -o $@ $<

.PHONY: tags TAGS
tags: TAGS
TAGS: $(MLMODULES:%=%.mli) $(MLMODULES:%=%.ml)
#	ocamltags $^
	otags $^

.PHONY: depend cpp
depend:
	$(OCAMLDEP) $(MLMODULES:%=%.mli) $(MLMODULES:%=%.ml) >Makefile.depend

Makefile.depend:
	$(OCAMLDEP) $(MLMODULES:%=%.mli) $(MLMODULES:%=%.ml) >Makefile.depend

-include Makefile.depend
