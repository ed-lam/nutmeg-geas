#include "solver/solver_data.h"
#include "solver/branch.h"

namespace phage {

class simple_branch : public brancher {
public:
  simple_branch(void) { }
   
  patom_t branch(solver_data* s) {
    // Do the predicates first
    for(pid_t pi = 2; pi < s->state.p_vals.size(); pi+=2) {
      pval_t lb = s->state.p_vals[pi];
      pval_t ub = pval_max - s->state.p_vals[pi+1];
      if(lb < ub) {
        return patom_t(pi, lb + (1 + ub - lb)/2);
      }
    }
    
    // Now go back to the Bools.
    for(int bi = 0; bi < s->state.b_assigns.size(); bi++) {
      if(s->state.b_assigns[bi] == l_Undef.to_int()) {
        return patom_t(0, bi); 
      }
    }
    return at_Undef;
  }
};

brancher* default_brancher(solver_data* s) {
  return new simple_branch();
}

patom_t branch(solver_data* s) {
  for(brancher* b : s->branchers) {
    patom_t p = b->branch(s);
    if(p != at_Undef)
      return p;
  }
  return s->last_branch->branch(s);
}

}
