#include <geas/engine/propagator.h>
#include <geas/solver/solver_data.h>

namespace geas {

propagator::propagator(solver_data* _s)
    : is_queued(false), prop_id(_s->propagators.size()), s(_s) {
//#ifdef PROOF_LOG
    cons_id = s->log.scope_constraint;
//#endif
    s->propagators.push(this);
//    queue_prop(); 
  }

void propagator::queue_prop(void) {
  if(!is_queued) {
    s->prop_queue.insert(this);
    is_queued = true;
  }
}

bool propagator::check_sat(void) { return check_sat(s->state.p_vals); }
bool propagator::execute(vec<clause_elt>& confl) {
  return propagate(confl);
}

}
