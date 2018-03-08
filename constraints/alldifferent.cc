#ifndef PHAGE_ALLDIFFERENT_H
#define PHAGE_ALLDIFFERENT_H

#include "mtl/bool-set.h"
#include "engine/propagator.h"
#include "engine/propagator_ext.h"
#include "vars/intvar.h"

namespace geas {
  
class alldiff_v : public propagator, public prop_inst<alldiff_v> {
  watch_result wake(int xi) {
    fixed.push(xi);
    queue_prop();
    return Wt_Keep; 
  }
public:
  alldiff_v(solver_data* s, vec<intvar>& _xs)
    : propagator(s), xs(_xs) {
    for(int ii : irange(xs.size())) {
      if(lb(xs[ii]) == ub(xs[ii])) {
        // Kill the value in other vars
        intvar::val_t k(lb(xs[ii]));
        for(int jj : irange(xs.size())) {
          if(ii == jj) continue;
          enqueue(*s, xs[jj] != k, reason());
        }
      } else {
        xs[ii].attach(E_FIX, watch<&P::wake>(ii, Wt_IDEM));
      }
    }
  }

  bool propagate(vec<clause_elt>& confl) {
    for(int xi : fixed) {
      intvar::val_t k(lb(xs[xi]));
      patom_t r(xs[xi] != k);
      assert(s->state.is_inconsistent(r));

      for(int ii : irange(xi)) {
        if(k < lb(xs[ii]) || ub(xs[ii]) < k)
          continue;
        if(!enqueue(*s, xs[ii] != k, r))
          return false;
      }
      for(int ii : irange(xi+1, xs.size())) {
        if(k < lb(xs[ii]) || ub(xs[ii]) < k)
          continue;
        if(!enqueue(*s, xs[ii] != k, r))
          return false;
      }
    }
    fixed.clear();

    return true;
  }

  void cleanup(void) {
    fixed.clear();
    is_queued = false;
  }

  vec<intvar> xs;

  vec<int> fixed;
};

class alldiff_b : public propagator {
  typedef typename intvar::val_t val_t;

  static watch_result wake_lb(void* ptr, int xi) {
    alldiff_b* p(static_cast<alldiff_b*>(ptr)); 
    p->queue_prop();
    p->lb_change.add(xi);
    return Wt_Keep;
  }
  static watch_result wake_ub(void* ptr, int xi) {
    alldiff_b* p(static_cast<alldiff_b*>(ptr)); 
    p->queue_prop();
    p->ub_change.add(xi);
    return Wt_Keep;
  }

  public: 
    alldiff_b(solver_data* s, vec<intvar>& _vs)
      : propagator(s), vs(_vs) {
      for(int ii : irange(vs.size())) {
        vs[ii].attach(E_LB, watch_callback(wake_lb, this, ii));
        vs[ii].attach(E_UB, watch_callback(wake_ub, this, ii));
        lb_ord.push(ii);
        ub_ord.push(ii);
        lbs.push(lb(vs[ii]));
        ubs.push(lb(vs[ii]));
      }
    }

    void root_simplify(void) {
      return; 
    }

    void cleanup(void) {
      is_queued = false;
      lb_change.clear();
      ub_change.clear();
    }
    
    struct bound_cmp {
      bound_cmp(vec<val_t>& _bs)
        : bounds(_bs) { }

      bool operator()(int ii, int jj) {
        return bounds[ii] < bounds[jj];  
      }
      vec<val_t>& bounds;
    };

    bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running alldiff]]" << std::endl;
#endif
      
      for(int ii : irange(vs.size())) {
        lbs[ii] = lb(vs[ii]);
        ubs[ii] = ub(vs[ii]);
      }
      std::sort(lb_ord.begin(), lb_ord.end(), bound_cmp(lbs));
      std::sort(ub_ord.begin(), ub_ord.end(), bound_cmp(ubs));

      // Do some stuff here  

      return true;
    }

    // Parameters
    vec<intvar> vs;

    // Temporary storage
    vec<int> lb_ord; // Vars orderd by lb
    vec<int> ub_ord; // Vars ordered by ub

    vec<val_t> lbs;
    vec<val_t> ubs;

    boolset lb_change;
    boolset ub_change;
};

bool all_different_int(solver_data* s, vec<intvar>& xs, patom_t r = at_True) {
  assert(r == at_True);

  // new alldiff_v(s, xs);
  // return true;
  return alldiff_v::post(s, xs);
}

}
#endif
