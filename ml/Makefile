include ../Makefile.config

CXX = g++
CXXFLAGS = -g -O3 -I .
CXXFLAGS += -Wall -Wno-non-virtual-dtor -Wno-unused-function -Wno-deprecated -ffast-math # -funroll-loops
CXXFLAGS += -I /usr/local/lib/ocaml -I /opt/local/lib/ocaml
CFLAGS = -g -O3 -I .
CFLAGS += -Wall -Wno-unused-function -Wno-deprecated -ffast-math
CFLAGS += -I /usr/local/lib/ocaml -I /opt/local/lib/ocaml
CFLAGS += -I ..
LFLAGS = -lz
OCAMLINC += -I ..

## Shared library generation
SHARED = gcc -shared
RANLIB = ranlib

#IDLSRCS = $(wildcard *.idl)
IDLSRCS = atom.idl solver.idl builtins.idl
MLIS = $(addsuffix .mli, $(basename $(IDLSRCS)))
MLS = $(addsuffix .ml, $(basename $(IDLSRCS)))
CMIS = $(addsuffix .cmi, $(basename $(IDLSRCS)))
CMOS = $(addsuffix .cmo, $(basename $(IDLSRCS)))
CMXS = $(addsuffix .cmx, $(basename $(IDLSRCS)))
STUBS = $(addsuffix _stubs.c, $(basename $(IDLSRCS)))
OBJS = $(addsuffix _stubs.o, $(basename $(IDLSRCS)))
#DEPS = $(addsuffix .d, $(basename $(IDLSRCS)))

MLLIBS = phage

MLTARGETS = $(addsuffix .cma, $(MLLIBS)) $(addsuffix .cmxa, $(MLLIBS))
LIBTARGETS = libphage_ml.a $(MLTARGETS)

all : $(LIBTARGETS) phage_top

#$(TESTS) : % : %.o $(OBJS)
#	$(CXX) $(CXXFLAGS) -o $@ $@.o $(OBJS) $(LFLAGS)

#libphage.a:
#	cp ../libphage.a .

$(STUBS) : $(MLIS)

%.ml %.mli : %.idl
	@echo Generating interfaces: " $^ "
	camlidl -no-include $^

phage.cma: $(CMIS) $(CMOS) libphage_ml.a ../libphage.a
	$(OCAMLC) $(OCAMLFLAGS) $(OCAMLINC) -custom -a -o $@ \
	$(CMOS) libphage_ml.a ../libphage.a \
	-ccopt "-L ." -cclib "-lcamlidl -lstdc++"

phage.cmxa phage.a: $(CMIS) $(CMXS) libphage_ml.a ../libphage.a
	$(OCAMLOPT) $(OCAMLOPTFLAGS) $(OCAMLINC) -a -o $@ \
	$(CMXS) libphage_ml.a ../libphage.a \
	-ccopt "-L . " -cclib "-lcamlidl -lstdc++"
	$(RANLIB) phage.a

libphage_ml.a: $(OBJS)
	$(AR) rcs $@ $^
	$(RANLIB) $@

libphage_ml.so: $(OBJS)
	$(SHARED) -o $@ $^

phage_top : $(LIBTARGETS)
	$(OCAMLMKTOP) $(OCAMLINC) -custom -o $@ \
	phage.a phage.cma \
  -ccopt "-L /opt/local/lib/ocaml" \
	-ccopt "-L . " -cclib "-lcamlidl -lstdc++"

clean :
	rm -f $(TARGETS) $(TARGETOBJS) $(TESTOBJS) $(OBJS)
	rm -f $(MLIS) $(MLS) $(CMIS) $(CMOS) $(CMXS) $(STUBS)
	rm -f *.annot *.o

clobber : clean
	rm -f $(LIBTARGETS)

-include $(DEPS)
-include $(TARGETDEPS)

%.d: %.cpp
	@$(CXX) -MM -MT  $(subst .d,.o,$@) -MT $@ $(CPPFLAGS) $< > $@

#---------------------------------------
# ML generic rules
#---------------------------------------

%.cmi: %.mli  $(DEPS)
	$(OCAMLC) $(OCAMLFLAGS) $(OCAMLINC) -c $<

%.cmo: %.ml %.cmi  $(DEPS)
	$(OCAMLC) $(OCAMLFLAGS) $(OCAMLINC) -c $<

%.cmx: %.ml %.cmi  $(DEPS)
	$(OCAMLOPT) $(OCAMLOPTFLAGS) $(OCAMLINC) -c $<
