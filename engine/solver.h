#ifndef __PHAGE_SOLVER_H__
#define __PHAGE_SOLVER_H__
#include "mtl/Queue.h"
#include "engine/atom.h"
#include "engine/manager.h"
#include "engine/env.h"
#include "engine/conflict.h"

// Class for performing the search.
class solver {
public:
  enum RESULT { UNSAT = 0, SAT = 1 };

  solver(env* _e);

  RESULT solve(void);

  int decisionLevel(void) { return e->level(); } 

  void post_atom(atom d, expln ex) {
    e->atom_trail.push(mk_inf(d, ex));
  }
  
protected:
  bool propagate(vec<atom>& confl);
  atom pick_branch(void);
  void post_branch(atom l);

  void backtrack_with(vec<atom>& out_learnt);
  void post_learnt(vec<atom>& out_learnt);

  env* e;
  int root;

  int atom_head;

  conflict_state confl_info;

  Queue<int> prop_queue;
};
#endif
