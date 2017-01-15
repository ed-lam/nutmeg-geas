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

static forceinline pval_t lb(solver_data* s, pid_t pi) {
  return s->state.p_vals[pi];
}
static forceinline pval_t ub(solver_data* s, pid_t pi) {
  return pval_max - s->state.p_vals[pi^1];
}

template<int ValC>
struct branch_val {
  static forceinline patom_t branch(solver_data* s, pid_t p) {
    switch(ValC) {
      case Val_Min:
        return ~patom_t(p, lb(s, p)+1);
      case Val_Max:
        return patom_t(p, ub(s, p));
      case Val_Split:
        {
          pval_t mid = lb(s, p) + ((ub(s, p) - lb(s, p) + 1)/2);
          return patom_t(p, mid);
        }
      case Val_Saved:
        {
          // pval_t saved = s->confl.pred_saved[p].val;
          pval_t saved = p&1 ? pval_inv(s->confl.pred_saved[p>>1].val)
                             : s->confl.pred_saved[p>>1].val;
          if(saved <= lb(s, p))
            // return ~patom_t(p, lb(s, p)+1);
            return le_atom(p, lb(s, p));
          if(ub(s, p) <= saved)
            // return patom_t(p, ub(s, p));
            return ge_atom(p, ub(s, p));
          // return patom_t(p, saved);
          // return ge_atom(p, saved);
          return le_atom(p, saved);
        }
      default:
        NOT_YET; 
        return at_Error;
    }
  }
};

template<int ValC>
class inorder_branch : public brancher {
public:
  inorder_branch(vec<pid_t>& _preds)
    : vars(_preds), start(0) { }

  patom_t branch(solver_data* s) {
    pid_t* p = vars.begin() + start;
    pid_t* end = vars.end();

    if(p == end)
      return at_Undef;
    
    if(lb(s, *p) != ub(s, *p))
      return branch_val<ValC>::branch(s, *p);

    patom_t at = at_Undef;
    for(++p; p != end; ++p) {
      if(lb(s, *p) != ub(s, *p)) {
        // Branch found
        at = branch_val<ValC>::branch(s, *p);  
        break;
      }
    }
    trail_change(s->persist, start, (unsigned int) (p - vars.begin()));
    return at;
  }
  
  vec<pid_t> vars;
  unsigned int start;
};

template<int VarC, int ValC>
class basic_branch : public brancher {
public:
  basic_branch(vec<pid_t>& _preds)
    : vars(_preds), start(0) { }

  forceinline pval_t score(solver_data* s, pid_t p) {
    switch(VarC) {
      case Var_Smallest:
        return lb(s, p);
      case Var_Largest:
        return pval_max - ub(s, p);
      case Var_FirstFail:
        return ub(s, p) - lb(s, p); 
      default:
        return 0;
    }
  }
   
  patom_t branch(solver_data* s) {
    pid_t* end = vars.end();

    pid_t* choice = end;
    pval_t choice_score = pval_err;
     
    pid_t* p = vars.begin() + start;
    for(; p != end; ++p) {
      if(lb(s, *p) == ub(s, *p))
        continue;
      pval_t p_score = score(s, *p);
      if(p_score < choice_score) {
        choice = p;
        choice_score = p_score;
      }
    }

    if(choice == end)
      return at_Undef;

    return branch_val<ValC>::branch(s, *choice);
  }

  vec<pid_t> vars;
  unsigned int start;
};

class seq_branch : public brancher {
public:
  seq_branch(vec<brancher*>& _bs)
    : branchers(_bs), start(0) { }

  patom_t branch(solver_data* s) {
    brancher** end = branchers.end();
    brancher** b = branchers.begin() + start;

    if(b == end)
      return at_Undef;
    
    patom_t at = (*b)->branch(s); 
    if(at != at_Undef)
      return at;

    for(++b; b != end; ++b) {
      at = (*b)->branch(s);
      if(at != at_Undef) {
        break; 
      }
    }
    
    trail_change(s->persist, start, ((unsigned int) (b - branchers.begin())));
    return at;
  }

  vec<brancher*> branchers;
  unsigned int start;
};

brancher* seq_brancher(vec<brancher*>& bs) {
  return new seq_branch(bs); 
}

class limit_branch : public brancher {
public:
  limit_branch(brancher* _b)
    : b(_b) { }

  patom_t branch(solver_data* s) {
    if(s->stats.restarts == 0)
      return b->branch(s);
    return at_Undef;
  }

  brancher* b;
};
brancher* limit_brancher(brancher* b) { return new limit_branch(b); }

brancher* select_inorder_brancher(ValChoice val_choice, vec<pid_t>& preds) {
  switch(val_choice) {
    case Val_Min:
      return new inorder_branch<Val_Min>(preds);
    case Val_Max:
      return new inorder_branch<Val_Max>(preds);
    case Val_Split:
      return new inorder_branch<Val_Split>(preds);
    case Val_Saved:
      return new inorder_branch<Val_Saved>(preds);
    default:
      NOT_YET;
      return nullptr;
  }
}

template<int VarC>
brancher* select_basic_brancher(ValChoice val_choice, vec<pid_t>& preds) {
  switch(val_choice) {
    case Val_Min:
      return new basic_branch<VarC, Val_Min>(preds);
    case Val_Max:
      return new basic_branch<VarC, Val_Max>(preds);
    case Val_Split:
      return new basic_branch<VarC, Val_Split>(preds);
    case Val_Saved:
      return new basic_branch<VarC, Val_Saved>(preds);
    default:
      NOT_YET;
      return nullptr;
  }
}

brancher* basic_brancher(VarChoice var_choice, ValChoice val_choice, vec<pid_t>& preds) {
  switch(var_choice) {
    case Var_InputOrder:
      return select_inorder_brancher(val_choice, preds);
    case Var_FirstFail:
      return select_basic_brancher<Var_FirstFail>(val_choice, preds);
    case Var_Smallest:
      return select_basic_brancher<Var_Smallest>(val_choice, preds);
    case Var_Largest:
      return select_basic_brancher<Var_Smallest>(val_choice, preds);
    default:
      NOT_YET;
      return nullptr;
  }
}

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
      
      // if(!pred_fixed(s, pi))
      if(!pred_fixed(s, pi<<1))
      {
        if(rem_count != removed.size()) {
          trail_push(s->persist, rem_count);
          rem_count = removed.size();
        }

        // Choose a value to branch on. Currently [| pi = lb(pi) |]
        // return ~patom_t(pi, pred_val(s, pi<<1)+1);
        return branch_val<Val_Min>::branch(s, pi<<1);
        // return branch_val<Val_Max>::branch(s, pi<<1);
        // return branch_val<Val_Saved>::branch(s, pi<<1);
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
