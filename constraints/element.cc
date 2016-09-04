#include <utility>
#include <algorithm>
#include "engine/propagator.h"
#include "solver/solver_data.h"
#include "vars/intvar.h"

namespace phage {

typedef std::pair<int, int> ipair;

void int_element(solver_data* s, intvar x, intvar z,
                   vec<int>& ys, int base) {
  // Also set domain of ys.
  x.set_lb(base, reason()); x.set_ub(base + ys.size()-1, reason());  
  // z.set_lb(ys_uniq[0], reason()); z.set_ub(ys_uniq.last(), reason());

  make_sparse(z, ys);

  for(int ii : irange(ys.size())) {
    add_clause(s, x != ii + base, z == ys[ii]);
  }

  vec<int> ys_uniq(ys); uniq(ys_uniq);

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
