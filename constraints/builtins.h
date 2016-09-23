#ifndef PHAGE_BUILTINS_H
#define PHAGE_BUILTINS_H
#include "vars/intvar.h"

namespace phage {
// linear.cc
void linear_le(solver_data* s, vec<int>& ks, vec<intvar>& vs, int k);

// element.cc
void int_element(solver_data* s, intvar x, intvar i, vec<int>& ys);
void var_int_element(solver_data* s, intvar x, intvar i, vec<intvar>& ys);

// disjunctive.cc
void disjunctive_int(solver_data* s, vec<intvar>& st, vec<int>& du); 
void disjunctive_var(solver_data* s, vec<intvar>& st, vec<intvar>& du);

// cumulative.cc
void cumulative(solver_data* s,
  vec<intvar>& starts, vec<int>& durations, vec<int>& resources, int cap);

// arith.cc
void int_max(solver_data* s, intvar z, vec<intvar>& xs);
bool int_abs(solver_data* s, intvar z, intvar x);
void int_mul(solver_data* s, intvar z, intvar x, intvar y);

// r -> (x < y)
bool int_le(solver_data* s, intvar x, intvar y, patom_t r = at_True);

// alldifferent.cc
void all_different(solver_data* s, vec<intvar>& xs);
}
#endif
