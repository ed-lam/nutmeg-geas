#include "mtl/Vec.h"
#include "solver/solver_data.h"
#include "vars/intvar.h"

namespace phage {
class int_linear_le : public propagator {
    static void wakeup(int_linear_le* prop, int i) {
      prop->queue_prop();          
    }

  public: 
    struct elt {
      elt(int _c, intvar _x)
        : c(_c), x(_x) { }
      int c;
      intvar x;
    };

    int_linear_le(solver_data* s, vec<int>& ks, vec<intvar>& vs, int _k)
      : propagator(s), k(_k) {
      for(int ii = 0; ii < vs.size(); ii++) {
        if(ks[ii] > 0) {
          xs.push(elt(ks[ii], vs[ii]));
        } else if(ks[ii] < 0) {
          ys.push(elt(-ks[ii], vs[ii]));
        }
      }
    }

    bool propagate(vec<clause_elt>& confl) {
      int lb = 0;
      for(elt e : xs)
        lb += e.c * e.x.lb();
      for(elt e : ys)
        lb -= e.c * e.x.ub();

      if(lb > k) {
        // Collect enough atoms to explain the sum.
        NOT_YET_WARN;
        return false; 
      }

      // Otherwise, propagate upper bounds.
      int slack = k - lb; 
      for(elt e : xs) {
        int x_ub = e.x.lb() + slack/e.c;
        if(x_ub < e.x.ub()) {
          // Build the explanation
          NOT_YET_WARN;
          reason r; 
          if(!e.x.set_ub(x_ub, r))
            return false;
        }
      }

      for(elt e : ys) {
        int x_lb = e.x.ub() - slack/e.c; 
        if(e.x.lb() < x_lb) {
          NOT_YET_WARN;
          reason r;
          if(!e.x.set_lb(x_lb, r))
            return false;
        }
      }
      return true;
    }

    vec<elt> xs;
    vec<elt> ys;
    int k;
};
}
