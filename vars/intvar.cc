#include "solver/solver_data.h"
#include "vars/intvar.h"

#include <cstdio>
#include <utility>

namespace phage {
#define intvar_base intvar

intvar_base::intvar_base(solver_data* _s, intvar_manager* _m, int _idx, pid_t _pid)
  : s(_s), man(_m), idx(_idx), pid(_pid)
{ assert(!(pid&1)); }

int64_t intvar_base::lb(void) const {
  return to_int(s->state.p_vals[pid]);
}

int64_t intvar_base::ub(void) const {
  return to_int(pval_max - s->state.p_vals[pid^1]);
}

bool intvar::is_fixed(void) const {
  return pred_fixed(s, pid);
  // return pval_max - s->state.p_vals[pid^1] == s->state.p_vals[pid];
}

int64_t intvar_base::lb_prev(void) const {
  return to_int(s->state.p_last[pid]);
}

int64_t intvar_base::ub_prev(void) const {
  return to_int(pval_max - s->state.p_last[pid^1]);
}

int64_t intvar_base::lb_0(void) const {
  return to_int(s->state.p_root[pid]);
}

int64_t intvar_base::ub_0(void) const {
  return to_int(pval_max - s->state.p_root[pid^1]);
}

bool intvar_base::set_lb(int64_t min, reason r) {
  return enqueue(*s, patom_t(pid, from_int(min)), r);
}

bool intvar_base::set_ub(int64_t max, reason r) {
  return enqueue(*s, patom_t(pid^1, pval_max - from_int(max)), r);
}

int64_t intvar_base::model_val(const model& m) const {
  return to_int(m.get(pid));
}

void intvar_base::attach(intvar_event e, watch_callback c) {
  man->attach(idx, e, c);
}

static void wakeup(void* ptr, int idx) {
  // This is a bit ugly
  intvar_manager* man = static_cast<intvar_manager*>(ptr);
  void* origin = man->s->active_prop;
  // Do some stuff
  int vi = idx>>1;
  if(pred_fixed(man->s, man->var_preds[vi])) {
    for(auto c : man->fix_callbacks[vi]) {
      if(!c.can_skip(origin))
        c();
    }
  }
  if(idx&1) {
    for(auto c : man->ub_callbacks[vi])
      if(!c.can_skip(origin))
        c();
  } else {
    for(auto c : man->lb_callbacks[vi])
      if(!c.can_skip(origin))
        c();
  }
//  printf("Ping: %d\n", idx);
}

intvar_manager::intvar_manager(solver_data* _s)
  : s(_s) { }
     
intvar intvar_manager::new_var(int64_t lb, int64_t ub) {
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

  s->state.p_last[p^1] = pval_max - from_int(ub);
  s->state.p_root[p^1] = pval_max - from_int(ub);

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

bool intvar_manager::in_domain(unsigned int vid, int64_t val) {
  pval_t pval = from_int(val);

  // If the eq-atom exists, [x = k] != False
  auto it = eqtable[vid].find(val);
  if(it != eqtable[vid].end())
    return !s->state.is_inconsistent((*it).second);

  // Otherwise, return lb(x) <= k <= ub(x)
  pid_t pid = var_preds[vid];
  return s->state.p_vals[pid] <= pval && pval <= pval_max - s->state.p_vals[pid^1];
}

patom_t intvar_manager::make_eqatom(unsigned int vid, int64_t ival) {
  // Find the appropriate var/val pair
  pid_t x_pi(var_preds[vid]);
  pval_t val(from_int(ival));

  auto it = eqtable[vid].find(val);
  if(it != eqtable[vid].end())
    return (*it).second;

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
bool intvar_manager::make_sparse(unsigned int vid, vec<int64_t>& ivals) {
   // Find the appropriate var/val pair
  pid_t x_pi(var_preds[vid]);

  vec<int64_t> vals;
  for(int64_t v : ivals)
    vals.push(from_int(v));
  uniq(vals);

  // Bind the LB and UB atoms.
  auto it = eqtable[vid].find(vals[0]);
  if(it == eqtable[vid].end()) {
    eqtable[vid].insert(std::make_pair(vals[0], le_atom(x_pi, vals[0])));
  }
  it = eqtable[vid].find(vals.last());
  if(it == eqtable[vid].end()) {
    eqtable[vid].insert(std::make_pair(vals.last(), ge_atom(x_pi, vals.last())));
  }

  // And set global bounds
  patom_t lb_at(ge_atom(x_pi, vals[0]));
  patom_t ub_at(le_atom(x_pi, vals.last()));
  if(!s->state.is_entailed(lb_at)) {
    if(!enqueue(*s, lb_at, reason()))
      return false;
  }
  if(!s->state.is_entailed(ub_at)) {
    if(!enqueue(*s, ub_at, reason()))
      return false;
  }

  for(int64_t vidx : irange(1, vals.size()-1)) {
    pval_t val(vals[vidx]);

    patom_t at;

    auto it = eqtable[vid].find(val);
    if(it != eqtable[vid].end()) {
      at = (*it).second;
      continue;
    } else {
      at = new_bool(*s);
      eqtable[vid].insert(std::make_pair(val, at));
    }

    // Connect the equality atom to the corresponding
    // bounds
    // Should return values
    add_clause(s, ~at, le_atom(x_pi, val));
    add_clause(s, ~at, ge_atom(x_pi, val));
    add_clause(s, at,
      le_atom(x_pi, vals[vidx-1]),
      ge_atom(x_pi, vals[vidx+1]));
  }
  return true;
}

}

