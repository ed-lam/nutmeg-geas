#ifndef PHAGE_ALLDIFFERENT_H
#define PHAGE_ALLDIFFERENT_H

#include "engine/propagator.h"
#include "vars/intvar.h"

namespace phage {
  
class alldiff_b : public propagator {
  static void wake(void* ptr, int xi) {
    alldiff_b* p(static_cast<alldiff_b*>(ptr)); 
    p->queue_prop();
  }

  public: 
    alldiff_b(solver_data* s, vec<intvar>& _vs)
      : propagator(s), vs(_vs) {
      for(int ii : irange(vs.size())) {
        vs[ii].attach(E_LU, watch_callback(wake, this, ii));
        lb_ord.push(ii);
        ub_ord.push(ii);
        lb.push(vs[ii].lb());
        ub.push(vs[ii].ub());
      }
    }

    void root_simplify(void) {
      return; 
    }
    
    struct bound_cmp {
      bound_cmp(vec<int64_t>& _bs)
        : bounds(_bs) { }

      bool operator()(int ii, int jj) {
        return bounds[ii] < bounds[jj];  
      }
      vec<int64_t>& bounds;
    };

    bool propagate(vec<clause_elt>& confl) {
      std::cout << "[[Running alldiff]]" << std::endl;
      
      for(int ii : irange(vs.size())) {
        lb[ii] = vs[ii].lb();
        ub[ii] = vs[ii].ub();           
      }
      std::sort(lb_ord.begin(), lb_ord.end(), bound_cmp(lb));
      std::sort(ub_ord.begin(), ub_ord.end(), bound_cmp(ub));

      // Do some stuff here  

      return true;
    }

    // Parameters
    vec<intvar> vs;

    // Temporary storage
    vec<int> lb_ord; // Vars orderd by lb
    vec<int> ub_ord; // Vars ordered by ub

    vec<int64_t> lb;
    vec<int64_t> ub;
};

}
#endif
