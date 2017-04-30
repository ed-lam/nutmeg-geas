#ifndef PHAGE_MDD_PROP_H
#define PHAGE_MDD_PROP_H
#include "engine/propagator.h"
#include "mtl/bool-set.h"
#include "vars/intvar.h"

namespace phage {

class mdd_prop : public propagator {
  class mdd;

  static watch_result wake(void* ptr, int xi) {
    mdd_prop* p(static_cast<mdd_prop*>(ptr));
    p->changes.add(xi);
    p->queue_prop();
    return Wt_Keep;
  }

  public: 
    struct valpair { int var; intvar::val_t val; };

    mdd_prop(solver_data* s, mdd& _m, vec<intvar>& _vs)
      : propagator(s), vs(_vs) {
      
      int idx = 0;
      for(int ii : num_range(vs.size())) {
        intvar v(vs[ii]);
        for(intvar::val_t k : v.domain(s)) {
          attach(s, v != k, watch_callback(wake, this, idx));
          valpairs.push( valpair {ii, k} );
          idx++;
        }
      }
    }

    void root_simplify(void) {
      
    }
    
    bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running mdd]]" << std::endl;
#endif

      return true;
    }

    // Persistent information
    vec<valpair> valpairs;
    vec<intvar> vs;

    // Transient data
    boolset changes;
};

}

#endif
