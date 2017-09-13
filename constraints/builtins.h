#ifndef PHAGE_BUILTINS_H
#define PHAGE_BUILTINS_H
#include "vars/intvar.h"

namespace phage {
// linear.cc
bool linear_le(solver_data* s, vec<int>& ks, vec<intvar>& vs, int k,
  patom_t r = at_True);
bool linear_ne(solver_data* s, vec<int>& ks, vec<intvar>& vs, int k,
  patom_t r = at_True);
// linear-ps.cc
bool linear_le_ps(solver_data* s, vec<int>& ks, vec<intvar>& vs, int k,
  patom_t r = at_True);

// bool-linear.cc
bool atmost_1(solver_data*, vec<patom_t>& xs, patom_t r = at_True);
bool atmost_k(solver_data*, vec<patom_t>& xs, int k, patom_t r = at_True);
bool bool_linear_le(solver_data* s, vec<int>& ks, vec<patom_t>& xs, int k, patom_t r = at_True);
bool bool_linear_ne(solver_data* s, vec<int>& ks, vec<patom_t>& xs, int k, patom_t r = at_True);

// element.cc
bool int_element(solver_data* s, intvar x, intvar i, vec<int>& ys,
  patom_t r = at_True);
bool var_int_element(solver_data* s, intvar x, intvar i, vec<intvar>& ys,
  patom_t r = at_True);

// disjunctive.cc
bool disjunctive_int(solver_data* s, vec<intvar>& st, vec<int>& du); 
bool disjunctive_var(solver_data* s, vec<intvar>& st, vec<intvar>& du);

// cumulative.cc
bool cumulative(solver_data* s,
  vec<intvar>& starts, vec<int>& durations, vec<int>& resources, int cap);

// arith.cc
bool int_max(solver_data* s, intvar z, vec<intvar>& xs, patom_t r = at_True);
bool int_abs(solver_data* s, intvar z, intvar x, patom_t r = at_True);
bool int_mul(solver_data* s, intvar z, intvar x, intvar y, patom_t r = at_True);
bool int_div(solver_data* s, intvar z, intvar x, intvar y, patom_t r = at_True);

// x <= y + k
// bool int_le(solver_data* s, intvar x, intvar y, intvar::val_t k);

// r -> (x <= y)
bool pred_le(solver_data* s, pid_t x, pid_t y, int k, patom_t r = at_True);
bool int_le(solver_data* s, intvar x, intvar y, int k, patom_t r = at_True);
bool int_ne(solver_data* s, intvar x, intvar y, patom_t r = at_True);
bool int_eq(solver_data* s, intvar x, intvar y, patom_t r = at_True);

// alldifferent.cc
bool all_different_int(solver_data* s, vec<intvar>& xs, patom_t r = at_True);
}
#endif
