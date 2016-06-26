#ifndef PHAGE_SOLVER_IMPL__H
#define PHAGE_SOLVER_IMPL__H
#include "mtl/Vec.h"
#include "mtl/Queue.h"
#include "engine/phage-types.h"
#include "engine/state.h"
#include "engine/infer.h"
#include "engine/propagator.h"

#include "solver/solver.h"

namespace phage {

class solver::solver_data {
public:
  solver_data(const solver::options& _opts)
    : opts(_opts)
  { }

  solver::options opts;
   
  pred_state state;
  infer_info infer;

  vec< vec<watch_callback> > bool_callbacks;
  vec< vec<watch_callback> > pred_callbacks;

  Queue<pid_t> pred_queue;
  vec<pid_t> wake_queue;
  Queue<propagator*> prop_queue;
};

bool enqueue(solver::solver_data& s, patom_t p, reason r);

}
#endif
