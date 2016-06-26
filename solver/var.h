#ifndef PHAGE_VAR__H
#define PHAGE_VAR__H

#include "engine/infer.h"
#include "solver/solver_data.h"

namespace phage {

class int_var {
  static const pval_t offset = ((pval_t) INT64_MIN); 

  static int64_t to_int(pval_t v) { return (int64_t) (offset + v); }
  static pval_t from_int(int64_t v) { return ((pval_t) v) - offset; }
public:
  int_var(solver::solver_data* _s, int64_t min, int64_t max)
    : s(_s), pid(_s->make_pred(((pval_t) min) - offset, ((pval_t) max) - offset))
  { assert(!(pid&1)); }


  inline lb(void) const {
    return to_int(s->state.p_vals[pid]);
  }

  inline ub(void) const {
    return to_int(pval_max - s->state.p_vals[pid]);
  }

  bool set_lb(int64_t min, reason r) {
    return enqueue(s, patom_t(pid, from_int(min)), r);
  }

  bool set_ub(int64_t max, reason r) {
    return enqueue(s, patom_t(pid^1, pval_max - from_int(min)), r);
  }

  solver::solver_data* s;
  pid_t pid;
};

}
#endif
