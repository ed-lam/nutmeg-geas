#ifndef PHAGE_STATE__H
#define PHAGE_STATE__H
#include "engine/phage-types.h"
#include "mtl/Vec.h"

namespace phage {

// Interpreting a pair of pvals as a range.
// Keeping persistent pvar_refs is probably risky,
// if new predicates are liable to be added.
class pvar_ref {
public: 
  pvar_ref(pval_t* _b) : base(_b) { }

  uint64_t lb(void) const { return base[0]; }  
  uint64_t ub(void) const { return pval_max - base[1]; }

  // Deal with trailing
  bool set_lb(uint64_t lb) {
    base[0] = lb;
    return lb <= pval_max - base[1];
  }
  bool set_ub(uint64_t ub) {
    base[1] = pval_max - ub;
    return base[0] <= ub;
  }
  pval_t* base;     
};

// Representing the current state of atomic predicates
class pred_state {
public:
  pred_state(void) {
    // Add Boolean placeholder
    new_pred();
  }

  // As with infer, preds are added in pairs.
  pid_t new_pred(void) {
    pid_t p = p_vals.size();
    p_vals.push(0);
    p_vals.push(0);

    p_last.push(0);
    p_last.push(0);

    p_root.push(0);
    p_root.push(0);
    return p;
  }

  bool pred_is_bool(pid_t pid) const { return pid <= 1; }

  bool is_entailed(patom_t atom) const {
    return atom.val <= p_vals[atom.pid];
  }
  bool is_inconsistent(patom_t atom) const {
    return pval_max - p_vals[atom.pid^1] < atom.val;
  }

  bool is_entailed_l0(patom_t atom) const {
    return atom.val <= p_root[atom.pid];
  }
  bool is_inconsistent_l0(patom_t atom) const {
    return pval_max - p_root[atom.pid^1] < atom.val;
  }

  pvar_ref get_ref(pid_t pi) {
    assert(!(pi&1)); // pi must be the base.
    return pvar_ref(&p_vals[pi]);
  }

  bool post(patom_t atom) {
    if(is_inconsistent(atom))
      return false;
    
    if(!is_entailed(atom))
      p_vals[atom.pid] = atom.val; 
    return true;
  }
  
  vec<lbool> b_assigns;
  vec<pval_t> p_vals; // Current values of predicates
  vec<pval_t> p_last; // Values at previous decision level
  vec<pval_t> p_root; // ...and at the root
};

}

#endif
