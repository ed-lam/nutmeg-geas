#ifndef PHAGE_SOLVER__H
#define PHAGE_SOLVER__H

// #include "solver/var.h"
#include "engine/phage-types.h"
#include "solver/expr.h"
#include "solver/model.h"
#include "solver/options.h"
#include "vars/intvar.h"

namespace phage {

class solver_data;

class solver {
public:
  // A model just stores the valuations
  // of atomic predicates
  enum result { SAT, UNSAT, UNKNOWN };

  solver(void);
  solver(options& opts);
  ~solver(void);

  intvar new_intvar(int64_t lb, int64_t ub);
  // Post a constraint
  // bool post(bexpr& e);

  // Solving
  result solve(void);

  // Retrieve a model
  model get_model(void);

  // Incremental interface:
  // push/retract assumptions
  bool assume(patom_t p);
  void retract(void);
  void clear_assumptions(void);

  void level_push(void);
  void level_pop(void);
  
  solver_data* data;  
  intvar_manager ivar_man;
};

}

#endif
