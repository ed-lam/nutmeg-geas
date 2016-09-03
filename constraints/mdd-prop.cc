#ifndef PHAGE_MDD_PROP_H
#define PHAGE_MDD_PROP_H
#include "engine/propagator.h"
#include "mtl/bool-set.h"
#include "vars/intvar.h"

namespace phage {

class mdd_prop : public propagator {
  class mdd;

  static void wake(void* ptr, int xi) {
    mdd_prop* p(static_cast<mdd_prop*>(ptr));
    p->changes.add(xi);
    p->queue_prop();
  }

  public: 
    struct valpair { int var; int64_t val; };

    mdd_prop(solver_data* s, mdd& _m, vec<intvar>& _vs)
      : propagator(s), vs(_vs) {
      
      int idx = 0;
      for(int ii : num_range(vs.size())) {
        intvar v(vs[ii]);
        for(int64_t k : v.domain()) {
          attach(s, v != k, watch_callback(wake, this, idx));
          valpairs.push( valpair {ii, k} );
          idx++;
        }
      }
    }

    void root_simplify(void) {
      
    }
    
    bool propagate(vec<clause_elt>& confl) {
      std::cout << "[[Running mdd]]" << std::endl;

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
