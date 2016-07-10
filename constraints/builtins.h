#ifndef PHAGE_BUILTINS_H
#define PHAGE_BUILTINS_H

namespace phage {
// linear.cc
void int_linear(solver_data* s, vec<int>& cs, vec<intvar>& xs, int k);

// element.cc
void int_element(solver_data* s, intvar x, intvar i, vec<int>& ys);
void var_int_element(solver_data* s, intvar x, intvar i, vec<intvar>& ys);

}
#endif
