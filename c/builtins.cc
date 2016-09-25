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
int linear_le(solver s, atom r, linterm* ts, int sz, int k) {
  vec<int> ks;
  vec<phage::intvar> xs;
  for(int ii = 0; ii < sz; ii++) {
    ks.push(ts[ii].c);
    xs.push(*get_intvar(ts[ii].x));
  }
  return phage::linear_le(get_solver(s)->data, ks, xs,  k, get_atom(r));
}

int int_mul(solver s, atom r, intvar z, intvar x, intvar y) {
  return phage::int_mul(get_solver(s)->data,
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

#ifdef __cplusplus
}
#endif
