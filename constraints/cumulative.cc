#include <algorithm>
#include "solver/solver_data.h"
#include "engine/propagator.h"
#include "engine/propagator_ext.h"
#include "constraints/builtins.h"

#include "mtl/bool-set.h"
#include "mtl/p-sparse-set.h"

namespace geas {

// Totally non-incremental time-table propagator.
class cumul_prop : public propagator, public prop_inst<cumul_prop> {
  enum LmarkT { L_ST, L_EN };
  struct landmark {
    int xi;
    LmarkT kind;
  };
  
  inline int m_st(int xi) {
    return ub(starts[xi]);
  }
  inline int m_en(int xi) {
    return lb(starts[xi]) + dur[xi];
  }

  int pos(landmark l) {
    switch(l.kind) {
      case L_EN:
        return 2*m_en(l.xi);
      case L_ST:
        return 2*m_st(l.xi)+1;
      default:
        NEVER;
    }
  }

  // explain start[xi] >= k.
  void ex_lb(int xi, pval_t p, vec<clause_elt>& expl) {
    int x_lb(starts[xi].lb_of_pval(p));

    int x_prev(lb(starts[xi]));
    // Need to explain why x <- [x_prev, x_lb) is infeasible.
    // Collect things
    int usage = res[xi];
    for(int xj : irange(starts.size())) {
      if(xj == xi)
        continue;
      if(m_st(xj) <= x_prev && x_lb <= m_en(xj)) {
        open.insert(xj);
        usage += res[xj];
      }
    }
    int slack = usage - (cap+1);
    int x_needed = 0;
    for(int xj : open) {
      if(res[xj] <= slack) {
        slack -= res[xj];
        continue;
      }
      int xj_time = x_lb - dur[xj];
      x_needed = std::max(x_needed, xj_time);
      expl.push(starts[xj] < xj_time);
    }
    open.clear();
    expl.push(starts[xi] < x_needed);
  }

  struct lmark_cmp {
    bool operator()(landmark x, landmark y) {
      return p->pos(x) < p->pos(y); 
    }

    cumul_prop* p;    
  };

  watch_result wake_s(int xi) {
    if(m_st(xi) < m_en(xi))
      queue_prop();

    return Wt_Keep;
  }

public:
  cumul_prop(solver_data* s, vec<intvar>& _starts, vec<int>& _dur, vec<int>& _res, int _cap)
    : propagator(s), starts(_starts), dur(_dur), res(_res), cap(_cap),
      open(_starts.size()),
      active_t(cmp_eet {this}), active_r(res_cmp_gt {res}),
      blocked(res_cmp_lt {res}) {

    for(int xi: irange(starts.size()))
      starts[xi].attach(E_LU, watch<&P::wake_s>(xi, Wt_IDEM));

    for(int ii : irange(starts.size())) {
      var_perm.push(ii);
    }
  }

  bool check_sat(void) {
    return true; 
  }

  // Relevant landmarks
  inline int est(int xi) const { return lb(starts[xi]); }
  inline int let(int xi) const { return ub(starts[xi]) + dur[xi]; }

  inline int m_st(int xi) const { return ub(starts[xi]); }
  inline int m_ed(int xi) const { return lb(starts[xi]) + dur[xi]; }

  struct cmp_est {
    bool operator()(int xi, int yi) { return p->est(xi) < p->est(yi); }
    P* p;
  };
  struct cmp_eet {
    bool operator()(int xi, int yi) { return p->m_ed(xi) < p->m_ed(yi); }
    P* p;
  };
  struct cmp_let {
    bool operator()(int xi, int yi) { return p->let(xi) > p->let(yi); }
    P* p;
  };
  struct cmp_lst {
    bool operator()(int xi, int yi) { return p->m_st(xi) > p->m_st(yi); }
    P* p;
  };

  struct res_cmp_gt {
    bool operator()(int xi, int yi) { return res[xi] > res[yi]; }
    vec<int>& res;
  };
  struct res_cmp_lt {
    bool operator()(int xi, int yi) { return res[xi] < res[yi]; }
    vec<int>& res;
  };

  void push_nonoverlap(int xi, int time, vec<clause_elt>& confl) {
    confl.push(starts[xi] > time);
    confl.push(starts[xi] <= time - dur[xi]);
  }

  bool propagate(vec<clause_elt>& confl) {
    // Set up the consumption profile  
    vec<landmark> lmarks;
    for(int xi : irange(starts.size())) {
      if(m_st(xi) < m_en(xi)) {
        lmarks.push(landmark { xi, L_ST });
        lmarks.push(landmark { xi, L_EN });
      }
    }
    std::sort(lmarks.begin(), lmarks.end(), lmark_cmp {this});
    std::sort(var_perm.begin(), var_perm.end(), cmp_est {this});
    
    int* v(var_perm.begin());
    int* ve(var_perm.end());
    
    // For now, just check: run a sweep, make sure capacity
    // is not exceeded.
    int margin = cap;
    for(int li : irange(lmarks.size())) {
      landmark l(lmarks[li]);
      switch(l.kind) {
        case L_ST:  
          {
            int time = m_st(l.xi);
            // Check for any active tasks which are
            // now finished.
            while(!active_t.empty() && m_en(active_t.getMin()) < time) {
              int r = active_t.removeMin();
              active_r.remove(r);
            }

            margin -= res[l.xi];
            
            if(margin < 0) {
              // Build the explanation.
              // Scan again to collect the open
              // activities.
              for(int lj = 0; lj < li; lj++) {
                switch(lmarks[lj].kind) {
                  case L_ST:
                    open.insert(lmarks[lj].xi);
                    break;
                  case L_EN:
                    open.remove(lmarks[lj].xi);
                    break;
                  default:
                    NEVER;
                }
              }
              open.insert(l.xi);
              int slack = -margin - 1; 
              for(int xi : open) {
                if(res[xi] <= slack) {
                  slack -= res[xi];
                  continue;
                }
                push_nonoverlap(xi, time, confl);    
              }
              open.clear();
              blocked.clear(); active_r.clear(); active_t.clear();
              return false;
            }

            // Usage has increased, so check if anything is
            // violated. 
            while(!active_r.empty() && res[active_r.getMin()] > margin) {
              int r = active_r.removeMin();
              active_t.remove(r);
              blocked.insert(r);
            }

            // Finally, check for any new tasks which need
            // to be activated
            for(; v != ve && est(*v) <= time; ++v) {
              // Already covered.
              if(m_ed(*v) <= time)
                continue;
              if(res[*v] > margin) {
                blocked.insert(*v);
              } else {
                active_r.insert(*v);
                active_t.insert(*v);
              }
            }
          }
          break;
        case L_EN:
          {
            int time = m_en(l.xi);
            margin += res[l.xi];
            while(!blocked.empty() && res[blocked.getMin()] <= margin) {
              int r = blocked.removeMin();
              assert(lb(starts[r]) < time);
              // Update the bound.
              if(!set_lb(starts[r], time, ex_thunk(ex<&P::ex_lb>, r, expl_thunk::Ex_BTPRED))) {
                blocked.clear(); active_t.clear(); active_r.clear();
                return false;
              }
              active_t.insert(r);
              active_r.insert(r);
            }
          }
          break;
        default:
          NEVER;
      }
    }

    blocked.clear(); active_r.clear(); active_t.clear();
    return true;
  }

protected:
  // Variables/static data
  vec<intvar> starts;
  vec<int> dur;
  vec<int> res;
  int cap;

  vec<int> var_perm;
  p_sparseset open;

  // Transient information during propagation
  Heap<cmp_eet> active_t;
  Heap<res_cmp_gt> active_r;
  Heap<res_cmp_lt> blocked;
};

bool cumulative(solver_data* s,
  vec<intvar>& starts, vec<int>& duration, vec<int>& resource, int cap) {
  // new cumul_prop(s, starts, duration, resource, cap);
  // return true;
  return cumul_prop::post(s, starts, duration, resource, cap);
}

}
