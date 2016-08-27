#include <map>
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
    
    template<class E>
    void make_expl(int var, int slack, E& ex) {
      vec<int> xs_pending;
      vec<int> ys_pending;
      // First, collect things we can omit entirely, or
      // include at the previous decision level
      for(int xi : irange(0, xs.size())) {
        if(2*xi == var)
          continue;
        elt e = xs[xi];

        int x_lb = e.x.lb();
        int x_lb_0 = e.x.lb_0();
        int diff_0 = e.c * (x_lb - x_lb_0);
        if(diff_0 <= slack) {
          slack -= diff_0;
          continue;
        }
        int x_lb_p = e.x.lb_prev();
        int diff_p = e.c * (x_lb - x_lb_p);
        if(diff_p < slack) {
          ex.push(e.x < x_lb_p); 
          continue;
        }
        xs_pending.push(xi);
      }
      for(int yi : irange(0, ys.size())) {
        if(2*yi+1 == var)
          continue;
        elt e = ys[yi];
        int y_ub = e.x.ub();
        int y_ub_0 = e.x.ub_0();
        int diff_0 = e.c * (y_ub_0 - y_ub);
        if(diff_0 <= slack) {
          slack -= diff_0;
          continue;
        }
        int y_ub_p = e.x.ub_prev();
        int diff_p = e.c * (y_ub_p - y_ub);
        if(diff_p < slack) {
          ex.push(e.x > y_ub_p);
          continue;
        }
        ys_pending.push(yi);
      }

      // Then, add things at the current level
      for(int xi : xs_pending) {
        elt e = xs[xi];
        int diff = slack/e.c;
        ex.push(e.x < e.x.lb() - diff);
        slack -= diff;
      }
      for(int yi : ys_pending) {
        elt e = ys[yi];
        int diff = slack/e.c;
        ex.push(e.x > e.x.ub() + diff);
        slack -= diff;
      }
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
        make_expl(-1, k - x_lb + y_ub, confl);
        return false; 
      }

      // Otherwise, propagate upper bounds.
      int slack = k - x_lb + y_ub;
      for(int xi : irange(0, xs.size())) {
        elt e = xs[xi];
        int x_diff = slack/e.c;
        int x_ub = e.x.lb() + x_diff;
        if(x_ub < e.x.ub()) {
          // Build the explanation
          expl_builder ex(s->persist.alloc_expl(xs.size()+ys.size()));
          make_expl(2*xi, slack - e.c * x_diff, ex);
          if(!e.x.set_ub(x_ub, *ex))
            return false;
        }
      }

      for(int yi : irange(0, ys.size())) {
        elt e = ys[yi];
        int y_diff = slack/e.c;
        int y_lb = e.x.ub() - y_diff;
        if(e.x.lb() < y_lb) {
          expl_builder ex(s->persist.alloc_expl(xs.size()+ys.size()));
          make_expl(2*yi+1, slack - e.c * y_diff, ex);
          if(!e.x.set_lb(y_lb, *ex))
            return false;
        }
      }
      return true;
    }

    vec<elt> xs;
    vec<elt> ys;
    int k;
};

// MDD-style decomposition.
// Introduce partial-sum variables, but coalesce ranges which
// are equivalent.
class linear_decomposer {
public:  
  linear_decomposer(solver_data* _s, vec<int>& _ks, vec<intvar>& _vs)
    : s(_s), ks(_ks), vs(_vs) { }

  void operator()(int k) {
    // Clear temporary state 
    tbl.clear();
    red_ubs.clear(); red_ubs.growTo(vs.size());
    feas_ubs.clear(); feas_ubs.growTo(vs.size());

    // Set up feasible ranges for partial sums
    int feas_ub = k;
    int red_ub = k;
    for(int r_ii : irange(1, vs.size()+1)) {
      int ii = vs.size() - r_ii;

      if(ks[ii] > 0) {
        red_ub -= ks[ii] * vs[ii].ub();
        feas_ub -= ks[ii] * vs[ii].lb();
      }
      if(ks[ii] < 0) {
        red_ub -= ks[ii] * vs[ii].lb();
        feas_ub -= ks[ii] * vs[ii].ub();
      }

      feas_ubs[ii] = feas_ub;
      red_ubs[ii] = red_ub;
    }
    
    if(red_ubs[0] < 0) {
      WARN("WARNING: Linear is satisfied by initial bounds.");
      return;
    }
    if(feas_ubs[0] < 0) {
      ERROR;
    }

    // Allocate partial sum predicates
    // Don't need first (since it's ks[0] * xs[0])
    // or last variable.
    for(int _ii : irange(vs.size()-2))
      ps_preds.push(new_pred(*s));

    NOT_YET_WARN;
      
    decompose(0, k);
  }
protected:
  struct entry_t {
    entry_t(int64_t _st, int64_t _en, pval_t _val)
      : st(_st), en(_en), val(_val) { }

    int64_t st, en;
    pval_t val;
  };

  int decompose(int idx, int64_t lim) {
    assert(idx < vs.size()); 
     
    return 0;       
  }

  solver_data* s; 
  vec<int>& ks;
  vec<intvar>& vs;

  std::map<int64_t, entry_t> tbl;
  // Upper bounds for feasibility and redundance
  vec<int64_t> red_ubs;
  vec<int64_t> feas_ubs;
  vec<pid_t> ps_preds;
};

void linear_le_dec(solver_data* s, vec<int>& ks, vec<intvar>& vs, int k) {
  linear_decomposer dec(s, ks, vs);
  dec(k);
}

void linear_le(solver_data* s, vec<int>& ks, vec<intvar>& vs, int k) {
  new int_linear_le(s, ks, vs, k);
}

}
