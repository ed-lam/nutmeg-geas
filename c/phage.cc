#include "solver/solver.h"
#include "solver/model.h"
#include "solver/branch.h"
#include "solver/priority-branch.h"
#include "engine/logging.h"

#include "utils/defs.h"

#include "c/phage.h"
#include "c/marshal.h"


#ifdef __cplusplus
extern "C" {
#endif

const atom at_True = unget_atom(phage::at_True);

atom neg(atom at) {
  return unget_atom(~get_atom(at));
}

pval_t pval_inv(pval_t p) { return phage::pval_inv(p); }
int64_t to_int(pval_t p) { return phage::to_int(p); }
//atom at_true(void) {
//    
//}

options default_opts(void) { return default_options; }
solver new_solver(options o) {
  return (solver) (new phage::solver(o));
}

void destroy_solver(solver s) {
  delete get_solver(s);
}

intvar new_intvar(solver s, int lb, int ub) {
  phage::solver* ps(get_solver(s));
  phage::intvar* v(new phage::intvar(ps->new_intvar(lb, ub)));
  return (intvar) v;
}

intvar intvar_neg(intvar x) {
  phage::intvar* v(new phage::intvar(-(*((phage::intvar*) x))));
  return (intvar) v;
}

intvar intvar_plus(intvar x, int k) {
  phage::intvar* v(new phage::intvar(*((phage::intvar*) x) + k));
  return (intvar) v;
}

int make_sparse(intvar px, int* vals, int sz) {
  phage::intvar* x((phage::intvar*) px);
  vec<phage::intvar::val_t> vs;
  for(int* v = vals; v < vals+sz; ++v)
    vs.push(*v);
  return phage::make_sparse(*x, vs);
}

void destroy_intvar(intvar v) {
  delete get_intvar(v);
}

fpvar new_floatvar(solver s, float lb, float ub) {
  phage::solver* ps(get_solver(s));
  phage::fp::fpvar* v(new phage::fp::fpvar(ps->new_floatvar(lb, ub)));
  return (fpvar) v;
}

void destroy_floatvar(fpvar v) {
  delete get_fpvar(v);
}

forceinline phage::VarChoice get_varc(var_choice c) {
  switch(c) {
    case VAR_INORDER: return phage::Var_InputOrder;
    case VAR_FIRSTFAIL: return phage::Var_FirstFail;
    case VAR_LEAST: return phage::Var_Smallest;
    case VAR_GREATEST: return phage::Var_Largest;
  }
  ERROR;
  return phage::Var_Smallest;
}

forceinline phage::ValChoice get_valc(val_choice c) {
  switch(c) {
    case VAL_MIN: return phage::Val_Min;
    case VAL_MAX: return phage::Val_Max;
    case VAL_SPLIT: return phage::Val_Split;
  }
  ERROR;
  return phage::Val_Min;
}

brancher new_int_brancher(var_choice varc, val_choice valc, intvar* vs, int sz) {
  vec<phage::pid_t> vars;
  intvar* end = vs+sz;
  for(; vs != end; ++vs)
    vars.push(get_intvar(*vs)->p);
  return ((brancher) phage::basic_brancher(get_varc(varc), get_valc(valc), vars));
}

brancher new_bool_brancher(var_choice varc, val_choice valc, atom* vs, int sz) {
  vec<phage::pid_t> vars;
  atom* end = vs+sz;
  for(; vs != end; ++vs)
    vars.push(get_atom(*vs).pid);
  return ((brancher) phage::basic_brancher(get_varc(varc), get_valc(valc), vars));
}

brancher new_bool_priority_brancher(var_choice varc,
  atom* vs, int vsz, brancher* bs, int bsz) {
  int sz = std::min(vsz, bsz);
  atom* end = vs + sz;
  vec<phage::patom_t> sel;
  vec<phage::brancher*> br;

  for(; vs != end; ++vs, ++bs) {
    sel.push(get_atom(*vs));
    br.push((phage::brancher*) (*bs));
  }
  return ((brancher) phage::priority_brancher(get_varc(varc), sel, br));
}

brancher new_int_priority_brancher(var_choice varc,
  intvar* vs, int vsz, brancher* bs, int bsz) {
  int sz = std::min(vsz, bsz);
  intvar* end = vs + sz;
  vec<phage::intvar> sel;
  vec<phage::brancher*> br;

  for(; vs != end; ++vs, ++bs) {
    sel.push(*get_intvar(*vs));
    br.push((phage::brancher*) (*bs));
  }
  return ((brancher) phage::priority_brancher(get_varc(varc), sel, br));
}

brancher seq_brancher(brancher* bs, int sz) {
  vec<phage::brancher*> branchers;
  brancher* end = bs + sz;
  for(; bs != end; ++bs)
    branchers.push((phage::brancher*) (*bs));
  return ((brancher) phage::seq_brancher(branchers));
}


brancher limit_brancher(brancher b) {
  return (brancher) phage::limit_brancher((phage::brancher*) b);
}

void add_brancher(solver s, brancher b) {
  get_solver(s)->data->branchers.push((phage::brancher*) b);
}

result solve(solver s, int lim) {
  // Currently ignoring conflict limit
  return unget_result(get_solver(s)->solve()); 
}

void abort_solve(solver s) { return get_solver(s)->abort(); }

void reset(solver s) {
  phage::solver_data* sd = get_solver(s)->data;
  if(sd->infer.trail_lim.size() > 0)
    phage::bt_to_level(sd, 0);
}

int post_atom(solver s, atom at) {
  reset(s);
  return get_solver(s)->post(get_atom(at));
}

int assume(solver s, atom at) {
  return get_solver(s)->assume(get_atom(at));
}
void retract(solver s) {
  get_solver(s)->retract();
}
void retract_all(solver s) {
  get_solver(s)->clear_assumptions();
}

void get_conflict(solver s, atom** at, int* out_sz) {
  vec<phage::patom_t> confl;
  get_solver(s)->get_conflict(confl);

  *out_sz = confl.size();
  *at = (atom*) malloc(sizeof(atom) * confl.size());
  for(int ii = 0; ii < confl.size(); ++ii) {
    (*at)[ii] = unget_atom(confl[ii]);
  }
}

int post_clause(solver s, atom* cl, int sz) {
  reset(s);
  vec<phage::clause_elt> elts;
  for(int ii : irange(sz))
    elts.push(get_atom(cl[ii]));
  return add_clause(*get_solver(s)->data, elts);
}

atom new_boolvar(solver s) {
  return unget_atom(get_solver(s)->new_boolvar());
}

void set_bool_polarity(solver s, atom at, int pol) {
  phage::solver_data* d = get_solver(s)->data;
  pid_t p = get_atom(at).pid;

  d->polarity[p>>1] = pol^(p&1);
  d->confl.pred_saved[p>>1].val = phage::from_int(p&1);
}

void set_int_polarity(intvar x, int pol) {
  phage::solver_data* d = get_intvar(x)->ext->s;
  pid_t p = get_intvar(x)->p;

  d->polarity[p>>1] = pol^(p&1);
  if(p&1)
    d->confl.pred_saved[p>>1].val = phage::pval_inv(d->state.p_root[p]);
  else
    d->confl.pred_saved[p>>1].val = d->state.p_root[p];
}

model get_model(solver s) {
  phage::model* m(new phage::model(get_solver(s)->get_model()));
  return (model) m;
}

void destroy_model(model m) {
  delete get_model(m);
}

int int_value(model m, intvar v) {
  return get_intvar(v)->model_val(*get_model(m));
}
float float_value(model m, fpvar v) {
  return get_fpvar(v)->model_val(*get_model(m));
}

pid_t ivar_pid(intvar v) { return get_intvar(v)->p; }

int ivar_lb(intvar v) {
  phage::solver_data* s = get_intvar(v)->ext->s;
  return get_intvar(v)->lb(s);
}
int ivar_ub(intvar v) {
  phage::solver_data* s = get_intvar(v)->ext->s;
  return get_intvar(v)->ub(s);
}

int atom_value(model m, atom at) {
  return get_model(m)->value(get_atom(at));
}

atom ivar_le(intvar v, int k) {
  return unget_atom( (*get_intvar(v)) <= k );
}

atom ivar_eq(intvar v, int k) {
  return unget_atom( (*get_intvar(v)) == k );
}

atom fpvar_le(fpvar v, float k) {
  return unget_atom( (*get_fpvar(v)) <= k );
}
atom fpvar_lt(fpvar v, float k) {
  return unget_atom( (*get_fpvar(v)) < k );
}

pred_t new_pred(solver s, int lb, int ub) {
  return phage::new_pred(*(get_solver(s)->data),
    phage::from_int(lb), phage::from_int(ub));
}

atom pred_ge(pred_t p, int k) {
  return unget_atom(phage::patom_t(p, k));
}

statistics get_statistics(solver s) {
  phage::solver_data* data(get_solver(s)->data);

  /*
  statistics st = {
    data->stats.solutions,
    data->stats.conflicts,
    data->stats.restarts
  };
  */
  return data->stats;
}

void set_cons_id(solver s, int id) {
  get_solver(s)->data->log.scope_constraint = id;
}

void set_log_file(solver s, FILE* f) {
  get_solver(s)->data->log.log_file = f;
}

#ifdef __cplusplus
}
#endif
