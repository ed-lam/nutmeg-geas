#include "solver/solver_data.h"
#include "vars/intvar.h"

#include <cstdio>

namespace phage {

intvar_base::intvar_base(solver_data* _s, int _idx, pid_t _pid)
  : s(_s), idx(_idx), pid(_pid)
{ assert(!(pid&1)); }

int64_t intvar_base::lb(void) const {
  return to_int(s->state.p_vals[pid]);
}

int64_t intvar_base::ub(void) const {
  return to_int(pval_max - s->state.p_vals[pid^1]);
}

bool intvar_base::set_lb(int64_t min, reason r) {
  return enqueue(*s, patom_t(pid, from_int(min)), r);
}

bool intvar_base::set_ub(int64_t max, reason r) {
  return enqueue(*s, patom_t(pid^1, pval_max - from_int(max)), r);
}

static void wakeup(void* ptr, int idx) {
  intvar_manager* man = static_cast<intvar_manager*>(ptr);
  // Do some stuff
  if(idx&1) {
    for(auto c : man->lb_callbacks[idx>>1])
      c(intvar_callback::E_LB);
  } else {
    for(auto c : man->ub_callbacks[idx>>1])
      c(intvar_callback::E_UB);
  }
  printf("Ping: %d\n", idx);
}

intvar_manager::intvar_manager(solver_data* _s)
  : s(_s) { }
     
intvar intvar_manager::new_var(int64_t lb, int64_t ub) {
  int idx = var_preds.size();
  pid_t p = new_pred(*s);
  // Register this as a watcher.
  // GKG: Perhaps defer this until something
  // is attached to the var
  s->pred_callbacks[p].push(watch_callback(wakeup, this, idx<<1));
  s->pred_callbacks[p+1].push(watch_callback(wakeup, this, (idx<<1)|1));

  lb_callbacks.push();
  ub_callbacks.push();

  // fprintf(stdout, "[%lld,%lld] ~~> [%lld, %lld]\n", lb, ub, intvar::from_int(lb), intvar::from_int(ub));
  // Set bounds
  intvar v(new intvar_base(s, idx, p));
  v.set_lb(lb, nullptr);
  v.set_ub(ub, nullptr);
  return v;
}

}

