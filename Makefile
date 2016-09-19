#CXX       = g++
#CXX       = g++-4.9
CXX       = clang++
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

#COPTIMIZE = -O3 -ffast-math -funroll-loops # -freorder-blocks-and-partition
#COPTIMIZE = -O2
COPTIMIZE = -O0
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
#TARGETS = $(TESTS)
LIB = libphage.a
all: $(TARGETS) $(LIB)

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

## Clean rule
clean:
	@rm -f $(TARGETS) $(LIB) phage.o $(COBJS) $(LIBOBJS) $(TESTOBJS) $(CDEPS) $(LIBDEPS) $(TESTDEPS)

-include $(CDEPS) $(LIBDEPS) $(TESTDEPS)
