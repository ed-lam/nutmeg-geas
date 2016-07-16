#ifndef PHAGE_BUILTINS_H
#define PHAGE_BUILTINS_H
#include "vars/intvar.h"

namespace phage {
// linear.cc
void linear_le(solver_data* s, vec<int>& ks, vec<intvar>& vs, int k);

// element.cc
void int_element(solver_data* s, intvar x, intvar i, vec<int>& ys);
void var_int_element(solver_data* s, intvar x, intvar i, vec<intvar>& ys);

// cumulative.cc
void cumulative(solver_data* s,
  vec<intvar>& starts, vec<int>& durations, vec<int>& resources, int cap);

// arith.cc
void int_max(solver_data* s, intvar z, vec<intvar>& xs);
}
#endif
