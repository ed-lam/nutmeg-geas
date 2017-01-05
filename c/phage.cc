#include "solver/solver.h"
#include "solver/model.h"
#include "solver/branch.h"
#include "engine/logging.h"

#include "c/phage.h"
#include "c/marshal.h"

#ifdef __cplusplus
extern "C" {
#endif

const atom at_True = unget_atom(phage::at_True);

atom neg(atom at) {
  return unget_atom(~get_atom(at));
}

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

forceinline phage::VarChoice get_varc(var_choice c) {
  switch(c) {
    case VAR_INORDER: return phage::Var_InputOrder;
    case VAR_FIRSTFAIL: return phage::Var_FirstFail;
    case VAR_LEAST: return phage::Var_Smallest;
    case VAR_GREATEST: return phage::Var_Largest;
  }
}

forceinline phage::ValChoice get_valc(val_choice c) {
  switch(c) {
    case VAL_MIN: return phage::Val_Min;
    case VAL_MAX: return phage::Val_Max;
    case VAL_SPLIT: return phage::Val_Split;
  }
}

brancher new_brancher(var_choice varc, val_choice valc, intvar* vs, int sz) {
  vec<phage::pid_t> vars;
  intvar* end = vs+sz;
  for(; vs != end; ++vs)
    vars.push(get_intvar(*vs)->pid);
  return ((brancher) phage::basic_brancher(get_varc(varc), get_valc(valc), vars));
}

brancher seq_brancher(brancher* bs, int sz) {
  vec<phage::brancher*> branchers;
  brancher* end = bs + sz;
  for(; bs != end; ++bs)
    branchers.push((phage::brancher*) (*bs));
  return ((brancher) phage::seq_brancher(branchers));
}

void add_brancher(solver s, brancher b) {
  get_solver(s)->data->branchers.push((phage::brancher*) b);
}

result solve(solver s, int lim) {
  // Currently ignoring conflict limit
  return unget_result(get_solver(s)->solve()); 
}

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

int ivar_lb(intvar v) {
  return get_intvar(v)->lb();
}
int ivar_ub(intvar v) {
  return get_intvar(v)->ub();
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
