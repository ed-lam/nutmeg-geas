#ifndef PHAGE_CONFLICT__H
#define PHAGE_CONFLICT__H

#include "mtl/p-sparse-set.h"
#include "engine/phage-types.h"
#include "engine/infer-types.h"

namespace phage {

class conflict_info {
public:
  void new_bool(void) {
    bool_seen.push(false);
  }
  void new_pred(void) {
    new_halfpred();
    new_halfpred();
  }

  void new_halfpred(void) {
    pred_seen.growTo(pred_eval.size());
    pred_eval.push(0);
    pred_hint.push(nullptr);
  }

  // Boolean fragment
  vec<bool> bool_seen;
  vec<unsigned int> bool_removed;
  
  // Predicate fragment
  p_sparseset pred_seen;
  vec<pval_t> pred_eval;
  vec<watch_node*> pred_hint;
  
  // Atoms at the current level
  int clevel;
};

// Returns the appropriate backtrack level.
int compute_learnt(solver_data* s, vec<clause_elt>& confl);
void reduce_db(solver_data* s);

}

#endif
