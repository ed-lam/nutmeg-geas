#ifndef __PHAGE_ENV_H__
#define __PHAGE_ENV_H__
// Solver environment.
// Mostly stores mapping of atom-kinds to
// managers, and the trail.
class env;

#include "mtl/Vec.h"
#include "utils/cache.h"
#include "engine/atom.h"
#include "engine/manager.h"
#include "engine/propagator.h"
#include "engine/trail.h"
#include "engine/branch.h"

#include "engine/expln.h"
#include "engine/sat.h"

class atom_inf {
public:
  atom_inf(atom _l, expln _ex)
    : l(_l), ex(_ex)
  { }

  atom l; 
  // Explanation thunk
  expln ex;
};

/*
inline atom_inf mk_inf(atom l, expln ex) {
  atom_inf inf; inf.l = l; inf.ex = ex; return inf;
}
*/

typedef struct {
  AtomManager* man;
  int ref;
} atomid_info;

typedef AutoC<atom, int>::cache atom_map_t;

class env {
public:
  env(void) { }

  // Allocate a new atom identifier, and
  // initialize the data-structures.
  atom_id new_atom_id(AtomManager* man, int ref);

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

  void attach(atom& a, Watcher* w, int tok);

  AtomManager* atom_man(atom& l);
  _atom to_atom_(atom& l);

  lbool atom_val(atom& l);

  int level(void) { return atom_tlim.size(); }

  // Mapping of managers for atoms
  // vec<AtomManager*> managers;
  vec<Brancher*> branchers;

  // List of propagators
  vec<Propagator*> propagators;

  // Information about allocated atom-ids.
  vec<atomid_info> atid_info;
  vec<bool> seen;
  vec<int> conflict_cookie;
  int num_seen;

  // Trail of inferences that were made.
  vec<int> atom_tlim;
  vec<atom_inf> atom_trail;

  // Data trail
  Trail gen_trail;
};

#endif
