#ifndef PRED__VAR_H
#define PRED__VAR_H
// Var-like interface for predicates.
// Saves us from having to wrap preds in intvars all the time.
#include "solver/solver_data.h"

namespace phage {

struct pred_var {
  typedef pval_t val_t;

  void attach(intvar_event e, watch_callback c) {
    if(e&E_LB) {
      s->pred_callbacks[p].push(c);  
    }
    if(e&E_UB) {
      s->pred_callbacks[p^1].push(c);  
    }
    if(e&E_FIX) {
      ERROR;
    }
  }

  pval_t model_val(const model& m) const { return m.get(p); }
  pval_t lb(ctx_t& ctx) const { return pred_lb(ctx, p); }
  pval_t ub(ctx_t& ctx) const { return pred_ub(ctx, p); }
  pval_t lb(solver_data* s) const { return lb(s->state.p_vals); }
  pval_t ub(solver_data* s) const { return ub(s->state.p_vals); }

  // GKG: These are a bit ugly.
  pval_t lb_delta(ctx_t& ctx, ctx_t& old) const {
    return ctx[p] - old[p];
  }
  pval_t ub_delta(ctx_t& ctx, ctx_t& old) const {
    return ctx[p^1] - old[p^1];
  }

  pval_t lb_of_pval(pval_t p) { return p;}
  pval_t ub_of_pval(pval_t p) { return pval_inv(p); }

  patom_t operator>=(int k) const { return ge_atom(p, k); }
  patom_t operator<=(pval_t k) const { return le_atom(p, k); }

  patom_t operator<(pval_t k) const { return this->operator<=(k-1); }
  patom_t operator>(pval_t k) const { return this->operator>=(k+1); }

  pid_t p;

  solver_data* s;
};

};
#endif
