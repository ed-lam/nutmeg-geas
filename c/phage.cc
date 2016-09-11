#include "solver/solver.h"
#include "solver/model.h"
#include "c/phage.h"
#include "c/marshal.h"

#ifdef __cplusplus
extern "C" {
#endif

atom neg(atom at) {
  return unget_atom(~get_atom(at));
}

//atom at_true(void) {
//    
//}

solver new_solver(void) {
  return (solver) (new phage::solver);
}

void destroy_solver(solver s) {
  delete get_solver(s);
}

intvar new_intvar(solver s, int lb, int ub) {
  phage::solver* ps(get_solver(s));
  phage::intvar* v(new phage::intvar(ps->new_intvar(lb, ub)));
  return (intvar) v;
}

void destroy_intvar(intvar v) {
  delete get_intvar(v);
}

result solve(solver s, int lim) {
  // Currently ignoring conflict limit
  return unget_result(get_solver(s)->solve()); 
}

int post_atom(solver s, atom at) {
  return get_solver(s)->post(get_atom(at));
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

int atom_value(model m, atom at) {
  return get_model(m)->value(get_atom(at));
}

atom ivar_le(intvar v, int k) {
  return unget_atom( (*get_intvar(v)) <= k );
}

atom ivar_eq(intvar v, int k) {
  return unget_atom( (*get_intvar(v)) == k );
}

#ifdef __cplusplus
}
#endif
