#include <utility>
#include <algorithm>
#include "engine/propagator.h"
#include "solver/solver_data.h"
#include "vars/intvar.h"

namespace phage {

typedef std::pair<int, int> ipair;

void uniq(vec<int>& ks) {
  std::sort(ks.begin(), ks.end());
  int jj = 1;
  for(int ii : num_range(1, ks.size())) {
    if(ks[ii] != ks[ii-1])
      ks[jj++] = ks[ii];
  }
  ks.shrink(ks.size() - jj);
}

void int_element(solver_data* s, intvar x, intvar z,
                   vec<int>& ys, int base) {
  vec<int> ys_uniq(ys);
  uniq(ys_uniq);

  // Also set domain of ys.
  x.set_lb(base, reason()); x.set_ub(base + ys.size()-1, reason());  
  z.set_lb(ys_uniq[0], reason()); z.set_ub(ys_uniq.last(), reason());

  for(int ii : irange(ys.size())) {
    add_clause(s, x != ii + base, z == ys[ii]);
  }

  for(int yy : ys_uniq) {
    vec<clause_elt> ps;
    ps.push(z != yy);
    for(int ii : irange(ys.size())) {
      if(ys[ii] == yy) {
        ps.push(x == ii + base);
      }
    }
    add_clause(*s, ps);
  }

  return;
}

void int_element(solver_data* s, intvar x, intvar z, vec<int>& ys) {
  int_element(s, x, z, ys, 1);
}

void intvar_element(solver_data* s, intvar x, intvar i, vec<intvar>& ys) {
  NOT_YET;
  return; 
}
}
