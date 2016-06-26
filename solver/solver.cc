#include "solver/solver.h"
#include "solver/solver_data.h"

namespace phage {

typedef solver::solver_data sdata;

solver::solver(void)
  : data(new solver_data(default_options)) {
   
}

solver::solver(options& _opts)
  : data(new solver_data(_opts)) {

}

inline bool is_bool(sdata& s, pid_t p) { return s.state.pred_is_bool(p); }

bool enqueue(sdata& s, patom_t p, reason r) {
  NOT_YET;
  if(is_bool(s, p.pid)) {
    return true; 
  } else {
    return true;
  }
}

inline bool propagate_pred(solver::solver_data& s, pid_t p) {
  NOT_YET;
  if(is_bool(s, p)) {
    return true; 
  } else {
    // Process 
    return true;
  }
}

inline void wakeup_pred(solver::solver_data& s, pid_t p) {
  assert(!is_bool(s, p)); // Handle Bool wake-up separately
  for(watch_callback call : s.pred_callbacks[p])
    call();
}

bool propagate(solver::solver_data& s) {
  // Propagate any entailed clauses
  while(!s.pred_queue.empty()) {
prop_restart:
    pid_t pi = s.pred_queue._pop();
    if(!propagate_pred(s, pi))
      return false;
  }
  
  // Fire any events for the changed predicates
  for(pid_t pi : s.wake_queue)
    wakeup_pred(s, pi);  
  s.wake_queue.clear();

  // Process enqueued propagators
  while(!s.prop_queue.empty()) {
    propagator* p = s.prop_queue._pop();
    if(!p->propagate(s.infer.confl))
      return false; 

    // If one or more predicates were updated,
    // jump back to 
    if(!s.pred_queue.empty())
      goto prop_restart;
  }

  return true;
}

// Solving
solver::result solver::solve(void) {
  return UNKNOWN;
}

// Retrieve a model
// precondition: last call to solver::solve returned SAT
solver::model solver::get_model(void) {
  model m;
  return m;   
}
   
// For incremental solving; any constraints
// added after a push are paired with an activation
// literal.
void solver::level_push(void) {
  NOT_YET;   
}

// Drop any constraints added at the current
// context. 
void solver::level_pop(void) {
  NOT_YET; 
}

// Post a constraint
/*
bool solver::post(bexpr& e) {
  return true;
}
*/

}
