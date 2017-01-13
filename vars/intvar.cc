#include "solver/solver_data.h"
#include "vars/intvar.h"

#include <cstdio>
#include <utility>

namespace phage {
#define intvar_base intvar

typedef intvar::val_t val_t;

intvar_base::intvar_base(solver_data* _s, intvar_manager* _m, int _idx, pid_t _pid)
  : s(_s), man(_m), idx(_idx), pid(_pid)
{ assert(!(pid&1)); }

/*
val_t intvar_base::lb(void) const {
  return to_int(s->state.p_vals[pid]);
}

val_t intvar_base::ub(void) const {
  return to_int(pval_max - s->state.p_vals[pid^1]);
}
*/

bool intvar::is_fixed(void) const {
  return pred_fixed(s, pid);
  // return pval_max - s->state.p_vals[pid^1] == s->state.p_vals[pid];
}

val_t intvar_base::lb_prev(void) const {
  return to_int(s->state.p_last[pid]);
}

val_t intvar_base::ub_prev(void) const {
  return to_int(pval_max - s->state.p_last[pid^1]);
}

val_t intvar_base::lb_0(void) const {
  return to_int(s->state.p_root[pid]);
}

val_t intvar_base::ub_0(void) const {
  return to_int(pval_max - s->state.p_root[pid^1]);
}

bool intvar_base::set_lb(val_t min, reason r) {
  return enqueue(*s, patom_t(pid, from_int(min)), r);
}

bool intvar_base::set_ub(val_t max, reason r) {
  return enqueue(*s, patom_t(pid^1, pval_max - from_int(max)), r);
}

val_t intvar_base::model_val(const model& m) const {
  return to_int(m.get(pid));
}

void intvar_base::attach(intvar_event e, watch_callback c) {
  man->attach(idx, e, c);
}

static watch_result wakeup(void* ptr, int idx) {
  // This is a bit ugly
  intvar_manager* man = static_cast<intvar_manager*>(ptr);
  void* origin = man->s->active_prop;
  // Do some stuff
  int vi = idx>>1;
  if(pred_fixed(man->s, man->var_preds[vi])) {
    run_watches(man->fix_callbacks[vi], origin);
  }
  if(idx&1) {
    run_watches(man->ub_callbacks[vi], origin);
  } else {
    run_watches(man->lb_callbacks[vi], origin);
  }
//  printf("Ping: %d\n", idx);
  return Wt_Keep;
}

intvar_manager::intvar_manager(solver_data* _s)
  : s(_s) { }
     
intvar intvar_manager::new_var(val_t lb, val_t ub) {
  int idx = var_preds.size();
  pid_t p = new_pred(*s);
  var_preds.push(p);
  eqtable.push_back(std::unordered_map<pval_t, patom_t>());
  // Register this as a watcher.
  // GKG: Perhaps defer this until something
  // is attached to the var
  s->pred_callbacks[p].push(watch_callback(wakeup, this, idx<<1));
  s->pred_callbacks[p+1].push(watch_callback(wakeup, this, (idx<<1)|1));

  lb_callbacks.push();
  ub_callbacks.push();
  fix_callbacks.push();

  // fprintf(stdout, "[%lld,%lld] ~~> [%lld, %lld]\n", lb, ub, intvar::from_int(lb), intvar::from_int(ub));
  // Set bounds
  // intvar v(new intvar_base(s, this, idx, p));
  intvar v(s, this, idx, p);
  v.set_lb(lb, reason());
  v.set_ub(ub, reason());
  // Also set the p_last and p_root values
  s->state.p_last[p] = from_int(lb);
  s->state.p_root[p] = from_int(lb);
  s->wake_vals[p] = from_int(lb);

  s->state.p_last[p^1] = pval_max - from_int(ub);
  s->state.p_root[p^1] = pval_max - from_int(ub);
  s->wake_vals[p^1] = pval_max - from_int(ub);
//  if(ub - lb < 100)
//    for(int ii : irange(lb, ub+1))  
//      make_eqatom(idx, ii);

  return v;
}

void intvar_manager::attach(unsigned int v_idx, intvar_event e, watch_callback c) {
  if(e&E_LB) {
    lb_callbacks[v_idx].push(c);  
  }
  if(e&E_UB) {
    ub_callbacks[v_idx].push(c);
  }
  if(e&E_FIX) {
    fix_callbacks[v_idx].push(c);
  }
}

bool intvar_manager::in_domain(unsigned int vid, val_t val) {
  pval_t pval = from_int(val);

  // If the eq-atom exists, [x = k] != False
  auto it = eqtable[vid].find(val);
  if(it != eqtable[vid].end())
    return !s->state.is_inconsistent((*it).second);

  // Otherwise, return lb(x) <= k <= ub(x)
  pid_t pid = var_preds[vid];
  return s->state.p_vals[pid] <= pval && pval <= pval_max - s->state.p_vals[pid^1];
}

patom_t intvar_manager::make_eqatom(unsigned int vid, val_t ival) {
  // Find the appropriate var/val pair
  pid_t x_pi(var_preds[vid]);
  pval_t val(from_int(ival));

  auto it = eqtable[vid].find(val);
  if(it != eqtable[vid].end())
    return (*it).second;

  // FIXME: Only safe at decision level 0.
  pval_t x_lb = s->state.p_vals[x_pi];
  pval_t x_ub = pval_max - s->state.p_vals[x_pi+1];
  if(val < x_lb || val > x_ub)
    return at_False;
  if(val == x_lb)
    return ~patom_t(x_pi, val+1);
  if(val == x_ub)
    return patom_t(x_pi, val);

  // Allocate the atom
  patom_t at(new_bool(*s));

  // Connect it to the corresponding bounds
  add_clause(s, ~at, patom_t(x_pi, val));
  add_clause(s, ~at, ~patom_t(x_pi, val+1));
  add_clause(s, at, ~patom_t(x_pi, val), patom_t(x_pi, val+1));

  eqtable[vid].insert(std::make_pair(val, at));

  // FIXME: Set up p_val, p_last, p_root and initializer
  return at;
}

// Should only be called at root level
bool intvar_manager::make_sparse(unsigned int vid, vec<val_t>& ivals) {
   // Find the appropriate var/val pair
  pid_t x_pi(var_preds[vid]);

  vec<pval_t> vals;
  for(val_t v : ivals)
    vals.push(from_int(v));
  uniq(vals);

  // Set global bounds and gaps
  if(!enqueue(*s, ge_atom(x_pi, vals[0]), reason()))
    return false;
  for(int vi = 1; vi < vals.size(); vi++) {
    if(vals[vi-1]+1 == vals[vi])
      continue;
    if(!add_clause(s, le_atom(x_pi, vals[vi-1]), ge_atom(x_pi, vals[vi])))
      return false;
  }
  if(!enqueue(*s, le_atom(x_pi, vals.last()), reason()))
    return false;

  // Bind the equality atoms
  auto it = eqtable[vid].find(to_int(vals[0]));
  if(it == eqtable[vid].end()) {
    patom_t at = le_atom(x_pi, vals[0]);
    eqtable[vid].insert(std::make_pair(to_int(vals[0]), at));
  }
  for(int vi = 1; vi < vals.size()-1; vi++) {
    auto it = eqtable[vid].find(to_int(vals[vi]));
    if(it != eqtable[vid].end())
      continue;

    patom_t at = new_bool(*s);
    eqtable[vid].insert(std::make_pair(to_int(vals[vi]), at));
    if(!add_clause(s, ~at, le_atom(x_pi, vals[vi])))
      return false;
    if(!add_clause(s, ~at, ge_atom(x_pi, vals[vi])))
      return false;
    if(!add_clause(s, at, le_atom(x_pi, vals[vi-1]), ge_atom(x_pi, vals[vi+1])))
      return false;
  }
  it = eqtable[vid].find(to_int(vals.last()));
  if(it == eqtable[vid].end()) {
    eqtable[vid].insert(std::make_pair(to_int(vals.last()), ge_atom(x_pi, vals.last())));
  }

  return true;
}

}

