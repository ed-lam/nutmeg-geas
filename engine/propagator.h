#ifndef PHAGE_PROPAGATOR__H
#define PHAGE_PROPAGATOR__H
#include "engine/infer-types.h"

namespace phage {
class solver_data;

class propagator {
public: 
  propagator(solver_data* _s)
    : s(_s) {
      
  }

  virtual bool propagate(vec<clause_elt>& confl) = 0;
  virtual bool check_sat(void) { return true; }
  virtual void root_simplify(void) { }
  virtual void cleanup(void) { is_queued = false; }

  void queue_prop(void);
protected:
  bool is_queued;
  solver_data* s;
};

}
#endif
