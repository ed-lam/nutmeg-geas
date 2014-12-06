#ifndef __PHAGE_ENV_H__
#define __PHAGE_ENV_H__
// Solver environment.
// Mostly stores mapping of atom-kinds to
// managers, and the trail.
class env;

typedef struct {
  char v;
} lbool;

#include "mtl/Vec.h"
#include "utils/cache.h"
#include "engine/atom.h"
#include "engine/manager.h"
#include "engine/propagator.h"
#include "engine/trail.h"
#include "engine/vTrail.h"
#include  "engine/clause.h"

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
typedef void(*expl_fun)(void* data, expl_cookie cookie, vec<atom>& out_expl);
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
  atom l; 
  // Explanation thunk
  expln ex;
} atom_inf;

inline atom_inf mk_inf(atom l, expln ex) {
  atom_inf inf; inf.l = l; inf.ex = ex; return inf;
}

typedef AutoC<atom, int>::cache atom_map_t;

class env {
public:
  env(void) { }

  // Register a manager.
  atom_kind reg(AtomManager* man)
  {
    atom_kind ret(managers.size());
    managers.push(man);
    return ret;
  }

  void push_level(void) {
    gen_trail.push_level();
    atom_tlim.push(atom_trail.size());
  }

  void pop_level(void) {
    gen_trail.restore_level();

    int lim = atom_tlim.last();
    while(atom_trail.size() > lim)
      atom_trail.pop();
  }

  lit lit_of_atom(atom& l);

  atom atom_of_lit(lit l)
  {
    atom atom(c_atoms[lvar(l)]);
    return lsgn(l) ? atom : ~atom;
  }

  // ALlocate a new clause-variable
  // identifier.
  int new_catom(atom l)
  {
    int id = c_atoms.size();
    c_atoms.push(l); 
    ws.push();
    return id;
  }

  lbool atom_val(atom& l);

  int level(void) { return atom_tlim.size(); }

  // Mapping of managers for atoms
  vec<AtomManager*> managers;

  // List of propagators
  vec<Propagator*> propagators;

  // Trail of inferences that were made.
  vec<int> atom_tlim;
  vec<atom_inf> atom_trail;

  // SAT subprobatom
  vec<atom> c_atoms; // Concretely instantiated atoms
  vec< vec<clause*> > ws;

  vec<clause*> clauses;
  vec<clause*> learnts;

  // Data trail
  Trail gen_trail;
  VTrail::Trail gen_vtrail;
};

#endif
