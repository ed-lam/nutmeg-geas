#include "mtl/Vec.h"
#include "utils/defs.h"

#include "c/atom.h"
#include "c/phage.h"
#include "c/builtins.h"

#include "c/marshal.h"

#include "solver/solver_data.h"
#include "constraints/builtins.h"

#ifdef __cplusplus
extern "C" {
#endif

/*
int clause(solver s, atom* cl, int sz) {
  vec<phage::clause_elt> elts;
  for(int ii : irange(sz))
    elts.push(get_atom(cl[ii]));
  return add_clause(*get_solver(s)->data, elts);
}
*/

// These are half-reified.
// For strict versions, call with r = at_True
int linear_le(solver s, atom r, int_linterm* ts, int sz, int k) {
  vec<int> ks;
  vec<phage::intvar> xs;
  for(int ii = 0; ii < sz; ii++) {
    ks.push(ts[ii].c);
    xs.push(*get_intvar(ts[ii].x));
  }
  return phage::linear_le(get_solver(s)->data, ks, xs,  k, get_atom(r));
}

int linear_ne(solver s, atom r, int_linterm* ts, int sz, int k) {
  vec<int> ks;
  vec<phage::intvar> xs;
  for(int ii = 0; ii < sz; ii++) {
    ks.push(ts[ii].c);
    xs.push(*get_intvar(ts[ii].x));
  }
  return phage::linear_ne(get_solver(s)->data, ks, xs,  k, get_atom(r));
}

int bool_linear_le(solver s, atom r, at_linterm* ts, int sz, int k) {
  vec<int> ks;
  vec<phage::patom_t> xs;
  for(int ii = 0; ii < sz; ii++) {
    ks.push(ts[ii].c);
    xs.push(get_atom(ts[ii].x));
  }
  return phage::bool_linear_le(get_solver(s)->data, ks, xs,  k, get_atom(r));
}
int atmost_1(solver s, atom r, atom* xs, int sz) {
  vec<phage::patom_t> ys;
  for(int ii : irange(sz))
    ys.push(get_atom(xs[ii]));
  return phage::atmost_1(get_solver(s)->data, ys, get_atom(r));
}

int atmost_k(solver s, atom r, atom* xs, int sz, int k) {
  vec<phage::patom_t> ys;
  for(int ii : irange(sz))
    ys.push(get_atom(xs[ii]));
  return phage::atmost_k(get_solver(s)->data, ys, k, get_atom(r));
}

int bool_linear_ne(solver s, atom r, at_linterm* ts, int sz, int k) {
  vec<int> ks;
  vec<phage::patom_t> xs;
  for(int ii = 0; ii < sz; ii++) {
    ks.push(ts[ii].c);
    xs.push(get_atom(ts[ii].x));
  }
  return phage::bool_linear_ne(get_solver(s)->data, ks, xs,  k, get_atom(r));
}


int int_mul(solver s, atom r, intvar z, intvar x, intvar y) {
  return phage::int_mul(get_solver(s)->data,
                        *get_intvar(z), *get_intvar(x), *get_intvar(y),
                        get_atom(r));
}
int int_div(solver s, atom r, intvar z, intvar x, intvar y) {
  return phage::int_div(get_solver(s)->data,
                        *get_intvar(z), *get_intvar(x), *get_intvar(y),
                        get_atom(r));
}

int int_abs(solver s, atom r, intvar z, intvar x) {
  return phage::int_abs(get_solver(s)->data,
                        *get_intvar(z), *get_intvar(x), get_atom(r));
}

int int_max(solver s, atom r, intvar z, intvar* xs, int sz) {
  vec<phage::intvar> p_xs;
  for(intvar* v = xs; v != xs+sz; ++v) {
    p_xs.push(*get_intvar(*v));
  }
  return phage::int_max(get_solver(s)->data,
                        *get_intvar(z), p_xs, get_atom(r));
}

int int_element(solver s, atom r, intvar z, intvar x, int* elts, int sz) {
  vec<int> p_elts;
  for(int* v = elts; v != elts+sz; ++v) {
    p_elts.push(*v);
  }
  return phage::int_element(get_solver(s)->data,
                        *get_intvar(z), *get_intvar(x), p_elts, get_atom(r));
}

int var_int_element(solver s, atom r, intvar z, intvar x, intvar* elts, int sz) {
  vec<phage::intvar> p_elts;
  for(intvar* v = elts; v != elts+sz; ++v) {
    p_elts.push(*get_intvar(*v));
  }
  return phage::var_int_element(get_solver(s)->data,
                        *get_intvar(z), *get_intvar(x), p_elts, get_atom(r));
}

int int_le(solver s, atom r, intvar x, intvar y, int k) {
  return phage::int_le(get_solver(s)->data,
                    *get_intvar(x), *get_intvar(y), k, get_atom(r));
}

int int_ne(solver s, atom r, intvar x, intvar y) {
  return phage::int_ne(get_solver(s)->data,
                    *get_intvar(x), *get_intvar(y), get_atom(r));
}
#ifdef __cplusplus
}
#endif
