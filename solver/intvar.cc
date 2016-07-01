#include "solver/intvar.h"
#include "solver/solver_data.h"

namespace phage {

intvar::intvar(solver_data* _s, pid_t _pid)
  : s(_s), pid(_pid)
{ assert(!(pid&1)); }

int64_t intvar::lb(void) const {
  return to_int(s->state.p_vals[pid]);
}

int64_t intvar::ub(void) const {
  return to_int(pval_max - s->state.p_vals[pid]);
}

bool intvar::set_lb(int64_t min, reason r) {
  return enqueue(*s, patom_t(pid, from_int(min)), r);
}

bool intvar::set_ub(int64_t max, reason r) {
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
  // Set bounds
  // Register this as a watcher.
  // GKG: Perhaps defer this until something
  // is attached to the var
  s->pred_callbacks[p].push(watch_callback(wakeup, this, idx<<1));
  s->pred_callbacks[p+1].push(watch_callback(wakeup, this, (idx<<1)|1));
  return intvar(s, p);
}

}

