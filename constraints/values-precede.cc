#include <algorithm>
#include <climits>
#include "engine/propagator.h"
#include "engine/propagator_ext.h"
#include "solver/solver_data.h"
#include "vars/intvar.h"
#include "mtl/bool-set.h"
#include "mtl/p-sparse-set.h"
#include "utils/interval.h"

namespace phage {

// Like vals-precede-chain, but just monotonically
// increasing.
class vals_precede_seq : public propagator,
  public prop_inst<vals_precede_seq> {
  enum { S_Nil = 0, S_Act = 1, S_Red = 2 };

  watch_result wake_dis(int xi) {
    set(status, (char) S_Red);
    return Wt_Keep;
  }
  watch_result wake_act(int xi) {
    set(status, (char) S_Act);
    queue_prop();
    return Wt_Keep;
  }

  watch_result wake_lb(int xi) {
    queue_prop();
    return Wt_Keep;
  }
  watch_result wake_ub(int xi) {
    queue_prop();
    return Wt_Keep;
  }

  void ex_ub(int xi, pval_t p, vec<clause_elt>& expl) {
    int u = xs[xi].ub_of_pval(p);
    int l = u-1;
    expl.push(~r);
    for(int ii : irange(xi))
      expl.push(xs[ii] >= l);
  }

  void ex_lb(int xi, pval_t p, vec<clause_elt>& expl) {
    NOT_YET;
  }
  void ex_r(int xi, pval_t _p, vec<clause_elt>& expl) {
    NOT_YET;
  }

public:
  vals_precede_seq(solver_data* s, vec<intvar>& _xs, patom_t _r)
    : propagator(s), r(_r), xs(_xs), cap(xs.size(), 0), status(S_Nil) {
    if(lb(r)) {
      status = S_Act;
    } else {
      attach(s, r, watch<&P::wake_act>(0, Wt_IDEM));
      attach(s, ~r, watch<&P::wake_dis>(0, Wt_IDEM));
    }

    for(int xi : irange(xs.size())) {
      xs[xi].attach(E_LB, watch<&P::wake_lb>(xi, Wt_IDEM));
      xs[xi].attach(E_UB, watch<&P::wake_ub>(xi, Wt_IDEM));
    }
  }
  
  bool check(void) const { return check(s->ctx()); }
  bool check(const ctx_t& ctx) const {
    int U = 0;
    for(intvar& x : xs) {
      if(x.lb(ctx) > U)
        return false;
      if(x.ub(ctx) >= U)
        U += 1;
    }
    return true;
  }

  bool propagate(vec<clause_elt>& elt) {
#ifdef LOG_PROP
    std::cout << "[[Running values_precede]]" << std::endl;
#endif
    int U = 0;

    if(!lb(r)) {
      // Not yet active
      for(int xi : irange(xs.size())) {
        if(lb(xs[xi]) > U) {
          if(!enqueue(*s, ~r, expl<&P::ex_r>(xi)))
            return false;
          set(status, (char) S_Red);
        }
        if(ub(xs[xi]) >= U)
          U++;
      }
      return true;
    }

    // Otherwise, do propagate.
    // Run forward, updating UBs
    for(int xi : irange(xs.size())) {
      if(ub(xs[xi]) > U) {
        if(!set_ub(xs[xi], U, expl<&P::ex_ub>(xi)))
          return false;
      }
      cap[xi] = U;
      if(ub(xs[xi]) >= U)
        U++;
    }
    // Now backward, updating LBs.
    int L = 0;
    for(int xi = xs.size()-1; xi > 0; xi--) {
      if(cap[xi-1] < L) {
        if(!set_lb(xs[xi], L, expl<&P::ex_lb>(xi))) {
          return false;
        }
      }
      if(ub(xs[xi]) >= L)
        L--;
    }
    return true;
  }

  void root_simplify(void) { }

  void cleanup(void) {
    is_queued = false;
  }

protected:
  patom_t r;
  vec<intvar> xs;

  vec<int> cap;

  // Persistent state
  Tchar status;
};

}
