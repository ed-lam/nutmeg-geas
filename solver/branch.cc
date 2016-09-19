#include "mtl/Heap.h"
#include "solver/solver_data.h"
#include "solver/branch.h"

namespace phage {

class simple_branch : public brancher {
public:
  simple_branch(void) { }
   
  patom_t branch(solver_data* s) {
    for(pid_t pi = 0; pi < s->state.p_vals.size(); pi+=2) {
      pval_t lb = s->state.p_vals[pi];
      pval_t ub = pval_max - s->state.p_vals[pi+1];
      if(lb < ub) {
        return patom_t(pi, lb + (1 + ub - lb)/2);
      }
    }
    
    return at_Undef;
  }
};

class pred_act_brancher : public brancher {
public:
  pred_act_brancher(solver_data* _s)
    : s(_s), rem_count(0) { }
  
  patom_t branch(solver_data* s) {
    // Restore not-necessarily-fixed predicates
    // upon backtracking
    if(rem_count < removed.size()) {
      for(int xi : irange(rem_count, removed.size())) {
        s->pred_heap.insert(removed[xi]);
      }
      removed.shrink(removed.size() - rem_count);
    }

    pid_t pi = pid_None;
    while(!s->pred_heap.empty()) {
      pi = s->pred_heap.getMin();
      
      if(!pred_fixed(s, pi)) {
        if(rem_count != removed.size()) {
          trail_push(s->persist, rem_count);
          rem_count = removed.size();
        }

        // Choose a value to branch on. Currently [| pi = lb(pi) |]
        // return patom_t(pi, pred_val(s, pi)+1);
        return ~patom_t(pi, pred_val(s, pi)+1);
      }

      s->pred_heap.removeMin();
      removed.push(pi);
    }
    // No preds remain
    return at_Undef;
  }

  solver_data* s;

  // Used for restoration 
  vec<int> removed;
  int rem_count;
};

class atom_act_brancher : public brancher {
public:
  atom_act_brancher(solver_data* _s)
    : s(_s) {
       
  }

  patom_t branch(solver_data* s) {
    NOT_YET;

  }

  solver_data* s;
};

brancher* pred_act_branch(solver_data* s) {
  return new pred_act_brancher(s);
}

brancher* atom_act_branch(solver_data* s);
brancher* default_brancher(solver_data* s) {
//  return new simple_branch();
  return pred_act_branch(s);
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
