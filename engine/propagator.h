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
  virtual ~propagator(void) { }

  virtual bool propagate(vec<clause_elt>& confl) = 0;
  virtual bool check_sat(void) { return true; }
  virtual void root_simplify(void) { }
  virtual void cleanup(void) { is_queued = false; }

  // execute dispatches between the checker (in a
  // half-reified case) and proapagator (when it's
  // active).
  // FIXME: Not yet implemented
  bool execute(vec<clause_elt>& confl);

  void queue_prop(void);

  bool is_queued;
protected:
  solver_data* s;
};

}
#endif
