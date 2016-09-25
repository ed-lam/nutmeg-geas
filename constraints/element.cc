#include <utility>
#include <algorithm>
#include "engine/propagator.h"
#include "solver/solver_data.h"
#include "vars/intvar.h"

namespace phage {

typedef std::pair<int, int> ipair;

void int_element(solver_data* s, patom_t r, intvar x, intvar z,
                   vec<int>& ys, int base) {
  // Also set domain of ys.
  if(s->state.is_entailed_l0(r)) {
    x.set_lb(base, reason()); x.set_ub(base + ys.size()-1, reason());  
    // z.set_lb(ys_uniq[0], reason()); z.set_ub(ys_uniq.last(), reason());

    make_sparse(z, ys);
  } else {
    add_clause(s, ~r, x >= base);
    add_clause(s, ~r, x < base + ys.size());

    vec<clause_elt> ps { ~r };
    for(int y : ys)
      ps.push(z == y);
    add_clause(*s, ps);
  }

  for(int ii : irange(ys.size())) {
    add_clause(s, ~r, x != ii + base, z == ys[ii]);
  }

  vec<int> ys_uniq(ys); uniq(ys_uniq);

  for(int yy : ys_uniq) {
    vec<clause_elt> ps { ~r };
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

void int_element(solver_data* s, intvar x, intvar z, vec<int>& ys, patom_t r) {
  int_element(s, r, x, z, ys, 1);
}

void intvar_element(solver_data* s, intvar x, intvar i, vec<intvar>& ys, patom_t r) {
  NOT_YET;
  return; 
}
}
