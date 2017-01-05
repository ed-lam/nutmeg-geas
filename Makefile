CXX       = g++
#CXX       = g++-4.9
#CXX       = clang++
MTL       = ./mtl
ENGINE	  = ./engine
SOLVER	  = ./solver
CONSTRAINTS = ./constraints
UTILS     = ./utils
VARS      = ./vars
CXXFLAGS    = -I . -Wall -Wno-deprecated # -ffloat-store
CXXFLAGS += --std=c++11
CXXFLAGS += -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS
LFLAGS    = -lz -Wall -Wno-deprecated
#LFLAGS   += -pg

#CXXFLAGS += -DPROOF_LOG

COPTIMIZE = -O3 -march=x86-64 -ffast-math -funroll-loops # -freorder-blocks-and-partition
#COPTIMIZE = -O2
#COPTIMIZE = -O0
CXXFLAGS += $(COPTIMIZE)
#CXXFLAGS += -ggdb -D DEBUG
CXXFLAGS += -ggdb
#CXXFLAGS += -pg

CSRCS     = $(wildcard $(ENGINE)/*.cc) $(wildcard $(VARS)/*.cc) $(wildcard $(SOLVER)/*.cc) $(wildcard $(CONSTRAINTS)/*.cc) $(wildcard $(UTILS)/*.cc)
COBJS     = $(addsuffix .o, $(basename $(CSRCS)))
CDEPS     = $(addsuffix .d, $(basename $(CSRCS)))

LIBSRCS = $(wildcard c/*.cc)
LIBOBJS = $(addsuffix .o, $(basename $(LIBSRCS)))
LIBDEPS = $(addsuffix .d, $(basename $(LIBSRCS)))

#TESTS = tests/TestVars tests/TestChain
TESTS = 
TESTSRC = $(wildcard tests/*.cc)
TESTOBJS = $(addsuffix .o, $(basename $(TESTSRC)))
TESTS = $(basename $(TESTSRC))
TESTDEPS = $(addsuffix .d, $(TESTS))

TARGETS = phage $(TESTS)
MLTARGETS = ml/libphage_ml.a ml/phage.cma ml/phage.cmxa ml/phage.a
FZN_TARGETS = fzn/fzn_phage fzn/fzn_phage.debug

#TARGETS = $(TESTS)
LIB = libphage.a
all: $(TARGETS) $(LIB) $(MLTARGETS) $(FZN_TARGETS)

## Dependencies
$(TESTS) : % : %.o $(COBJS)
phage:			phage.o $(COBJS)

.PHONY: all clean tests

## Build rule
%.o:	%.cc %.d
	@echo Compiling: "$@ ( $< )"
	@$(CXX) $(CXXFLAGS) -c -o $@ $<

## Dependency rules.
### Note that this doesn't update dependencies if something new is
### introduced into an indirectly included header file.
%.d: %.cc
	@echo Building dependencies: "$@ ( $< )"
	@$(CXX) -MM -MT  $(subst .d,.o,$@) -MT $@ $(CXXFLAGS) $< > $@

## Linking rules
$(TARGETS):
	@echo Linking: "$@ ( $^ )"
	@$(CXX) $^ $(LFLAGS) -o $@

libphage.a: $(COBJS) $(LIBOBJS)
	@echo Archiving: "$@ ( $^ )"
	ar rc $@ $^
	ranlib $@

ml/libphage_ml.a ml/phage.a ml/phage.cmxa ml/phage.cma : libphage.a
	@echo Building ML interface
	$(MAKE) -C $(@D) $(@F)

$(FZN_TARGETS) : % : $(LIB) $(ML_TARGETS) 
	@echo Building FZN interface
	$(MAKE) -C $(@D) $(@F)

## Clean rule
clean:
	$(MAKE) -C ml clean
	$(MAKE) -C fzn clean
	@rm -f $(TARGETS) $(LIB) phage.o $(COBJS) $(LIBOBJS) $(TESTOBJS) $(CDEPS) $(LIBDEPS) $(TESTDEPS)

clobber: clean
	$(MAKE) -C ml clobber
	$(MAKE) -C fzn clobber


-include $(CDEPS) $(LIBDEPS) $(TESTDEPS)
