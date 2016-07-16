#include "mtl/Vec.h"
#include "solver/solver_data.h"
#include "vars/intvar.h"

namespace phage {
class int_linear_le : public propagator {
  static void wake_x(void* ptr, int xi) {
    int_linear_le* p(static_cast<int_linear_le*>(ptr)); 
    p->queue_prop();     
  }
  static void wake_y(void* ptr, int yi) {
    int_linear_le* p(static_cast<int_linear_le*>(ptr)); 
    p->queue_prop();     
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
          vs[ii].attach(E_LB, watch_callback(wake_x, this, xs.size()));
          xs.push(elt(ks[ii], vs[ii]));
        } else if(ks[ii] < 0) {
          vs[ii].attach(E_UB, watch_callback(wake_y, this, ys.size()));
          ys.push(elt(-ks[ii], vs[ii]));
        }
      }
    }

    void root_simplify(void) {

    }

    bool propagate(vec<clause_elt>& confl) {
      std::cout << "[[Running linear]]" << std::endl;
      int x_lb = 0;
      for(elt e : xs)
        x_lb += e.c * e.x.lb();
      int y_ub = 0;
      for(elt e : ys)
        y_ub += e.c * e.x.ub();

      if(x_lb - y_ub  > k) {
        // Collect enough atoms to explain the sum.
        // FIXME: This is kinda weak. We really want to
        // push as much as we can onto the previous level.
        int x_needed = k - y_ub;
        for(elt e : xs) {
          confl.push(e.x < e.x.lb());
          x_needed -= e.c * e.x.lb();
          if(x_needed <= 0)
            break;
        }

        int y_needed = y_ub + x_needed;
        for(elt e : ys) {
          confl.push(e.x > e.x.ub());
          y_needed -= e.c * e.x.ub();
          if(y_needed <= 0)
            break;
        }
        return false; 
      }

      // Otherwise, propagate upper bounds.
      int slack = k - x_lb + y_ub;
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

void linear_le(solver_data* s, vec<int>& ks, vec<intvar>& vs, int k) {
  new int_linear_le(s, ks, vs, k);
}

}
