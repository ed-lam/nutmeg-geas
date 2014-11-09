#ifndef __PHAGE_ENV_H__
#define __PHAGE_ENV_H__
// Solver environment.
// Mostly stores mapping of lemma-kinds to
// managers, and the trail.
class env;

#include "mtl/Vec.h"
#include "engine/lemma.h"
#include "engine/manager.h"
#include "engine/propagator.h"
#include "engine/trail.h"
#include  "engine/clause.h"

typedef struct {
  char v;
} lbool;

static lbool mk_lbool(int v) { lbool l; l.v = v; return l; }
static lbool l_False = mk_lbool(-1);
static lbool l_True = mk_lbool(1);
static lbool l_Undef = mk_lbool(0);
inline lbool lbool_of_bool(bool b) {
  return mk_lbool(2*b - 1);
}

enum expl_kind { Ex_Dec, Ex_Cl, Ex_Fun };
enum expl_tag { Ex_Keep = 1 };
typedef int expl_cookie;

// Definition of deferred explanations.
typedef void(*expl_fun)(void* data, expl_cookie cookie, vec<lemma>& out_expl);
typedef int expl_cookie;
typedef struct {
  expl_fun fun;       // The function to call
  void* data;         // Typically the propagator
  expl_cookie cookie; // Typically the variable index
} ex_thunk;

typedef struct {
  expl_kind kind;
  union {
    ex_thunk ex;
    clause* cl;
  };
} expln;

typedef struct {
  lemma l; 
  // Explanation thunk
  expln ex;
} lem_inf;

inline lem_inf mk_inf(lemma l, expln ex) {
  lem_inf inf; inf.l = l; inf.ex = ex; return inf;
}

class env {
public:
  env(void) { }

  // Register a manager.
  lem_kind reg(LemmaManager* man)
  {
    lem_kind ret(managers.size());
    managers.push(man);
    return ret;
  }

  void push_level(void) {
    gen_trail.push_level();
    lem_tlim.push(lem_trail.size());
  }

  void pop_level(void) {
    gen_trail.restore_level();

    int lim = lem_tlim.last();
    while(lem_trail.size() > lim)
      lem_trail.pop();
  }
  

  int level(void) { return lem_tlim.size(); }

  // Mapping of managers for lemmas
  vec<LemmaManager*> managers;

  // List of propagators
  vec<Propagator*> propagators;

  // Trail of inferences that were made.
  vec<int> lem_tlim;
  vec<lem_inf> lem_trail;

  // Data trail
  Trail gen_trail;
};

#endif
