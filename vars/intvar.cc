#include "solver/solver_data.h"
#include "vars/intvar.h"

#include <cstdio>
#include <utility>

#define ADD(T, K, V) (T).add((K),(V))
// #define ADD(T, K, V) (T).insert(std::make_pair((K),(V)))
#define VAL(It) (It).value
// #define VAL(It) (It).second
namespace phage {

typedef intvar::val_t val_t;

void* create_ivar_man(solver_data* s) {
  return new intvar_manager(s);  
}

void destroy_ivar_man(void* ptr) {
  delete static_cast<intvar_manager*>(ptr);
}

static man_id_t iman_id = register_manager(create_ivar_man, destroy_ivar_man);

intvar_manager* get_ivar_man(solver_data* s) { return static_cast<intvar_manager*>(s->managers[iman_id].ptr); }

val_t intvar::model_val(const model& m) const {
  return to_int(m.get(p))+off;
}

void intvar::attach(intvar_event e, watch_callback c) {
  // man->attach(idx, e, c);
  if(e&E_LB) {
    ext->b_callbacks[p&1].push(c);  
  }
  if(e&E_UB) {
    ext->b_callbacks[(p&1)^1].push(c);
  }
  if(e&E_FIX) {
    ext->fix_callbacks.push(c);
  }
}

// Make this a static method of ivar_ext instead.
static watch_result wakeup(void* ptr, int idx) {
  // This is a bit ugly
  intvar_manager* man = static_cast<intvar_manager*>(ptr);
  void* origin = man->s->active_prop;
  // Do some stuff
  int vi = idx>>1;
  if(pred_fixed(man->s, man->var_preds[vi])) {
    // run_watches(man->fix_callbacks[vi], origin);
    run_watches(man->var_exts[vi]->fix_callbacks, origin);
  }
  run_watches(man->var_exts[vi]->b_callbacks[idx&1], origin);

  return Wt_Keep;
}

intvar_manager::intvar_manager(solver_data* _s)
  : s(_s) { }
     
intvar intvar_manager::new_var(val_t lb, val_t ub) {
  int idx = var_preds.size();
  pid_t p = new_pred(*s, from_int(lb), from_int(ub));
  var_preds.push(p);
  ivar_ext* ext(new ivar_ext(s, p, idx));
  var_exts.push(ext);

  // Register this as a watcher.
  // GKG: Perhaps defer this until something
  // is attached to the var
  s->pred_callbacks[p].push(watch_callback(wakeup, this, idx<<1));
  s->pred_callbacks[p+1].push(watch_callback(wakeup, this, (idx<<1)|1));

  // Set bounds
  intvar v(p, 0, ext);

  return v;
}

#if 0
bool intvar_manager::in_domain(unsigned int vid, val_t val) {
  /*
  pval_t pval = from_int(val);

  // If the eq-atom exists, [x = k] != False
  auto it = eqtable[vid].find(val);
  if(it != eqtable[vid].end())
    return !s->state.is_inconsistent((*it).second);

  // Otherwise, return lb(x) <= k <= ub(x)
  pid_t pid = var_preds[vid];
  return s->state.p_vals[pid] <= pval && pval <= pval_max - s->state.p_vals[pid^1];
  */
  assert(0);
  return false;
}

static pval_t init_lb(void* ptr, int ei, vec<pval_t>& vals) {
  /*
  intvar_manager* man(static_cast<intvar_manager*>(ptr));
  intvar_manager::eq_info info = man->eqinfo[ei];
  if(pred_lb(man->s, info.pid) < info.val)
    return from_int(0);
  if(pred_ub(man->s, info.pid) > info.val)
    return from_int(0);
  return from_int(1);
  */
  assert(0);
  return from_int(0);
}
static void ex_lb(void* ptr, int ei, pval_t val, vec<clause_elt>& elts) {
  /*
  intvar_manager* man(static_cast<intvar_manager*>(ptr));
  intvar_manager::eq_info info = man->eqinfo[ei];
  elts.push(le_atom(info.pid, info.val-1));
  elts.push(ge_atom(info.pid, info.val+1));
  */
  assert(0);
}


static pval_t init_ub(void* ptr, int ei, vec<pval_t>& vals) {
  /*
  intvar_manager* man(static_cast<intvar_manager*>(ptr));
  intvar_manager::eq_info info = man->eqinfo[ei];
  if(pred_lb(man->s, info.pid) > info.val)
    return pval_inv(from_int(0));
  if(pred_ub(man->s, info.pid) < info.val)
    return pval_inv(from_int(0));
  return pval_inv(from_int(1));
  */
  assert(0);
  return from_int(0);
}

static void ex_ub(void* ptr, int ei, pval_t val, vec<clause_elt>& elts) {
  /*
  intvar_manager* man(static_cast<intvar_manager*>(ptr));
  intvar_manager::eq_info info = man->eqinfo[ei];
  if(pred_lb(man->s, info.pid) > info.val) {
    elts.push(le_atom(info.pid, info.val));
  } else {
    assert(pred_ub(man->s, info.pid) < info.val);
    elts.push(ge_atom(info.pid, info.val));
  }
  */
  assert(0);
}

patom_t intvar_manager::make_eqatom(unsigned int vid, val_t ival) {
  /*
  // Find the appropriate var/val pair
  pid_t x_pi(var_preds[vid]);
  pval_t val(from_int(ival));

  auto it = eqtable[vid].find(val);
  if(it != eqtable[vid].end())
    return (*it).second;

  // FIXME: Only safe at decision level 0.
  pval_t x_lb = s->state.p_root[x_pi];
  pval_t x_ub = pval_inv(s->state.p_root[x_pi+1]);

  if(val < x_lb || val > x_ub)
    return at_False;
  if(val == x_lb)
    return ~patom_t(x_pi, val+1);
  if(val == x_ub)
    return patom_t(x_pi, val);

  // Allocate the atom
  // patom_t at(new_bool(*s));
  int eq_idx = eqinfo.size();
  pred_init in_lb(init_lb, this, eq_idx,
    expl_thunk {ex_lb, this, eq_idx});
  pred_init in_ub(init_ub, this, eq_idx,
    expl_thunk {ex_ub, this, eq_idx});
  eqinfo.push({ x_pi, val });
  patom_t at(new_bool(*s, in_lb, in_ub));

  // Connect it to the corresponding bounds
  add_clause_(s, ~at, patom_t(x_pi, val));
  add_clause_(s, ~at, ~patom_t(x_pi, val+1));
  add_clause_(s, at, ~patom_t(x_pi, val), patom_t(x_pi, val+1));

  eqtable[vid].insert(std::make_pair(val, at));

  // FIXME: Set up p_val, p_last, p_root and initializer
  return at;
  */
  assert(0);
  return at_False;
}
#endif

// Should only be called at root level
#if 0
bool intvar_manager::make_sparse(unsigned int vid, vec<val_t>& ivals) {
   // Find the appropriate var/val pair
   /*
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
  */
  assert(0);
  return true;
}
#endif

void ivar_ext::make_eager(void) {
  // Find the appropriate var/val pair
  pval_t lb(pred_lb(s, p));
  pval_t ub(pred_ub(s, p));

  for(pval_t ii = lb; ii <= ub; ii++) {
    get_eqatom(ii);
  }
}

bool ivar_ext::make_sparse(vec<pval_t>& _vs) {
  // Only safe at decision level 0.
  vec<pval_t> vs(_vs); 
  uniq(vs);
  // Make the watch-maps sparse.
// #if 0
  s->infer.make_sparse(p, vs);
  vec<pval_t> inv_vs;
  for(int ii = vs.size()-1; ii >= 0; --ii)
    inv_vs.push(pval_inv(vs[ii]));
  s->infer.make_sparse(p^1, inv_vs);

  // Set global bounds and gaps
  if(!enqueue(*s, ge_atom(p, vs[0]), reason()))
    return false;
#ifndef SPARSE_WATCHES
  // Now done in make_sparse.
  for(int vi = 1; vi < vs.size(); vi++) {
    if(vs[vi-1]+1 == vs[vi])
      continue;
    if(!add_clause(s, le_atom(p, vs[vi-1]), ge_atom(p, vs[vi])))
      return false;
  }
#endif
  if(!enqueue(*s, le_atom(p, vs.last()), reason()))
    return false;

  // Bind the equality atoms
  auto it = eqtable.find(vs[0]);
  if(it == eqtable.end()) {
    patom_t at = le_atom(p, vs[0]);
    // eqtable.insert(std::make_pair(vs[0], at));
    ADD(eqtable, vs[0], at);
  }
  for(int vi = 1; vi < vs.size()-1; vi++) {
    auto it = eqtable.find(vs[vi]);
    if(it != eqtable.end())
      continue;

    patom_t at = new_bool(*s);
    // eqtable.insert(std::make_pair(vs[vi], at));
    ADD(eqtable, vs[vi], at);
    if(!add_clause(s, ~at, le_atom(p, vs[vi])))
      return false;
    if(!add_clause(s, ~at, ge_atom(p, vs[vi])))
      return false;
    if(!add_clause(s, at, le_atom(p, vs[vi-1]), ge_atom(p, vs[vi+1])))
      return false;
  }
  it = eqtable.find(vs.last());
  if(it == eqtable.end()) {
    // eqtable.insert(std::make_pair(vs.last(), ge_atom(p, vs.last())));
    ADD(eqtable, vs.last(), ge_atom(p, vs.last()));
  }

  return true;
}

static pval_t eqat_init_lb(void* ptr, int ei, vec<pval_t>& vals) {
  ivar_ext* ext(static_cast<ivar_ext*>(ptr));
  if(pred_lb(vals, ext->p) < ext->vals[ei])
    return from_int(0);
  if(pred_ub(vals, ext->p) > ext->vals[ei])
    return from_int(0);
  return from_int(1);
}

static void eqat_ex_lb(void* ptr, int ei, pval_t val, vec<clause_elt>& elts) {
  ivar_ext* ext(static_cast<ivar_ext*>(ptr));
  elts.push(le_atom(ext->p, ext->vals[ei]-1));
  elts.push(ge_atom(ext->p, ext->vals[ei]+1));
}


static pval_t eqat_init_ub(void* ptr, int ei, vec<pval_t>& vals) {
  ivar_ext* ext(static_cast<ivar_ext*>(ptr));
  if(pred_lb(vals, ext->p) > ext->vals[ei])
    return pval_inv(from_int(0));
  if(pred_ub(vals, ext->p) < ext->vals[ei])
    return pval_inv(from_int(0));
  return pval_inv(from_int(1));
}

static void eqat_ex_ub(void* ptr, int ei, pval_t val, vec<clause_elt>& elts) {
  ivar_ext* ext(static_cast<ivar_ext*>(ptr));
  if(pred_lb(ext->s, ext->p) > ext->vals[ei]) {
    elts.push(le_atom(ext->p, ext->vals[ei]));
  } else {
    assert(pred_ub(ext->s, ext->p) < ext->vals[ei]);
    elts.push(ge_atom(ext->p, ext->vals[ei]));
  }
}

static void eqat_finalize_lb(solver_data* s, void* ptr, int ei) {
  ivar_ext* ext(static_cast<ivar_ext*>(ptr));
  pid_t x_pi = ext->p;
  pval_t val = ext->vals[ei];
  // patom_t at((*(ext->eqtable.find(val))).second);
  patom_t at(VAL(*(ext->eqtable.find(val))));
  add_clause_(s, at, ~patom_t(x_pi, val), patom_t(x_pi, val+1));
}

static void eqat_finalize_ub(solver_data* s, void* ptr, int ei) {
  ivar_ext* ext(static_cast<ivar_ext*>(ptr));
  pid_t x_pi = ext->p;
  pval_t val = ext->vals[ei];
//  patom_t at((*(ext->eqtable.find(val))).second);
  patom_t at(VAL(*(ext->eqtable.find(val))));
  add_clause_(s, ~at, patom_t(x_pi, val));
  add_clause_(s, ~at, ~patom_t(x_pi, val+1));
}

patom_t ivar_ext::get_eqatom(pval_t val) {
  auto it = eqtable.find(val);
  if(it != eqtable.end())
    // return (*it).second;
    return VAL(*it);

  int eq_idx = vals.size();
  vals.push(val);

  pval_t x_lb = s->state.p_root[p];
  pval_t x_ub = pval_inv(s->state.p_root[p+1]);

  if(val < x_lb || val > x_ub)
    return at_False;
  if(val == x_lb)
    return ~patom_t(p, val+1);
  if(val == x_ub)
    return patom_t(p, val);

  pred_init in_lb(eqat_init_lb, this, eq_idx,
    expl_thunk {eqat_ex_lb, this, eq_idx},
    eqat_finalize_lb);
  pred_init in_ub(eqat_init_ub, this, eq_idx,
    expl_thunk {eqat_ex_ub, this, eq_idx},
    eqat_finalize_ub);

  patom_t at = new_bool(*s, in_lb, in_ub);

  // Connect it to the corresponding bounds
  if(!s->state.is_inconsistent(at)) {
    add_clause_(s, ~at, patom_t(p, val));
    add_clause_(s, ~at, ~patom_t(p, val+1));
  }
  if(!s->state.is_entailed(at)) {
    add_clause_(s, at, ~patom_t(p, val), patom_t(p, val+1));
  }

  // eqtable.insert(std::make_pair(val, at));
  ADD(eqtable, val, at);
  return at;
}

intvar new_intvar(solver_data* s, intvar::val_t lb, intvar::val_t ub) {
  return get_ivar_man(s)->new_var(lb, ub);
}

}

