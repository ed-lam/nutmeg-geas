#ifndef PHAGE_SOLVER__H
#define PHAGE_SOLVER__H

// #include "solver/var.h"
#include "engine/phage-types.h"
#include "solver/expr.h"
#include "solver/model.h"
#include "solver/options.h"
#include "vars/intvar.h"
#include "vars/fpvar.h"

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

  intvar new_intvar(intvar::val_t lb, intvar::val_t ub);
  fp::fpvar new_floatvar(fp::val_t lb, fp::val_t ub);
  patom_t new_boolvar(void);
  // Post a constraint
  // bool post(bexpr& e);
  // Assert an atom unconditionally
  bool post(patom_t p);

  // Solving
  result solve(unsigned int conflict_limit = 0);
  void abort(void);

  // Retrieve a model
  model get_model(void);

  // Incremental interface:
  // push/retract assumptions
  bool assume(patom_t p);
  void retract(void);
  void push_assump_ctx(void);
  void pop_assump_ctx(void);
  void clear_assumptions(void);
  void get_conflict(vec<patom_t>& atom);

  void level_push(void);
  void level_pop(void);
  
  solver_data* data;  
//  intvar_manager ivar_man;
};

}

#endif
