#include "engine/propagator.h"
#include "solver/solver_data.h"
#include "vars/intvar.h"

namespace phage {
void int_element(solver_data* s, intvar x, intvar i, vec<int>& ys) {
  // Check whether ys is monotone.
  bool inc = true;
  bool dec = true;
  for(int yi = 1; yi < ys.size(); yi++) {
    if(ys[yi-1] < ys[yi])
      dec = false;
    else if(ys[yi-1] > ys[yi])
      inc = false;
  }

  if(inc) {
    int jj = 0;
    do {
      int val(ys[jj]);
      int ii = jj;
      while(ii < ys.size() && ys[ii] == val)
        ii++;

      add_clause(s, i < jj, x >= val);
      add_clause(s, x < val, i >= jj);

      jj = ii;
    } while(jj < ys.size());
    i.set_lb(0, reason());
    i.set_ub(ys.size()-1, reason());
    if(x.lb() < ys[0])
      x.set_lb(ys[0], reason());
    if(ys.last() < x.ub())
      x.set_ub(ys.last(), reason());
  } else if (dec) {
    NOT_YET;
  } else {
    NOT_YET;
  }
  return;
}

void intvar_element(solver_data* s, intvar x, intvar i, vec<intvar>& ys) {
  NOT_YET;
  return; 
}
}
