#ifndef __PHAGE_SOLVER_H__
#define __PHAGE_SOLVER_H__
#include "mtl/Queue.h"
#include "engine/lemma.h"
#include "engine/manager.h"
#include "engine/env.h"

// Class for performing the search.
class solver {
public:
  enum RESULT { SAT, UNSAT };

  solver(env* _e)
    : e(_e), root(0), lem_head(0)
  {

  }

  RESULT solve(void);

  int decisionLevel(void) { return e->level(); } 

  void post_lemma(lemma d, expln ex) {
    e->lem_trail.push(mk_inf(d, ex));
  }
  
protected:
  bool propagate(vec<lemma>& confl);
  lemma pick_branch(void);
  void post_branch(lemma l);
  void analyzeConflict(vec<lemma>& confl, vec<lemma>& out_learnt);
  void backtrack_with(vec<lemma>& out_learnt);
  void post_learnt(vec<lemma>& out_learnt);

  env* e;
  int root;

  int lem_head;

  Queue<int> prop_queue;
};
#endif
