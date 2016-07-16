#include "engine/propagator.h"
#include "solver/solver_data.h"

namespace phage {

void propagator::queue_prop(void) {
  if(!is_queued) {
    s->prop_queue.insert(this);
    is_queued = true;
  }
}

bool propagator::execute(vec<clause_elt>& confl) {
  return propagate(confl);
}

}
