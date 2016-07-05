#CXX       = g++
#CXX       = g++-4.9
CXX       = clang++
MTL       = ./mtl
ENGINE	  = ./engine
SOLVER	  = ./solver
UTILS     = ./utils
VARS      = ./vars
CXXFLAGS    = -I . -Wall -Wno-deprecated # -ffloat-store
CXXFLAGS += --std=c++11
CXXFLAGS += -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS
#CXXFLAGS += $(shell guile-config compile)
LFLAGS    = -lz -Wall -Wno-deprecated
#LFLAGS += $(shell guile-config link)
#LFLAGS   += -pg

#COPTIMIZE = -O3 -ffast-math -funroll-loops # -freorder-blocks-and-partition
#COPTIMIZE = -O2
COPTIMIZE = -O0
CXXFLAGS += $(COPTIMIZE)
#CXXFLAGS += -ggdb -D DEBUG
CXXFLAGS += -ggdb
#CXXFLAGS += -pg

CSRCS     = $(wildcard $(ENGINE)/*.cc) $(wildcard $(VARS)/*.cc) $(wildcard $(SOLVER)/*.cc) $(wildcard $(UTILS)/*.cc)
COBJS     = $(addsuffix .o, $(basename $(CSRCS)))
CDEPS     = $(addsuffix .d, $(basename $(CSRCS)))

# CHDRS      = $(wildcard $(ENGINE)/*.h) $(wildcard $(UTILS)/*.h) $(wildcard $(VARS)/*.h)

SATSRCS   = 
SATOBJS 	= $(addsuffix .o, $(basename $(SATSRCS)))
SATDEPS   = $(addsuffix .d, $(basename $(SATSRCS)))

SCMSRCS = $(wildcard scm/*.cc)
SCMOBJS	= $(addsuffix .o, $(basename $(SCMSRCS)))
SCMDEPS = $(addsuffix .d, $(basename $(SCMSRCS)))

#TESTS = tests/TestVars tests/TestChain
TESTS = 
TESTSRC = $(wildcard tests/*.cc)
TESTOBJS = $(addsuffix .o, $(basename $(TESTSRC)))
TESTS = $(basename $(TESTSRC))
TESTDEPS = $(addsuffix .d, $(TESTS))

TARGETS = phage $(TESTS)
#TARGETS = $(TESTS)
all: $(TARGETS)

## Dependencies
$(TESTS) : % : %.o $(COBJS)
phage:			phage.o $(SCMOBJS) $(COBJS)

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

## Clean rule
clean:
	@rm -f $(TARGETS) $(COBJS) $(SATOBJS) $(TESTOBJS) $(SCMOBJS) *.core $(CDEPS) $(SATDEPS) $(SCMDEPS) $(TESTDEPS)

-include $(CDEPS) $(TESTDEPS) $(SATDEPS) $(SCMDEPS)
