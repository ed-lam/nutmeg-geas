#ifndef PHAGE_SOLVER__H
#define PHAGE_SOLVER__H

// #include "solver/var.h"
#include "solver/expr.h"

namespace phage {

class solver {
public:
  class solver_data;
  class options;

  // Fill in.
  class model {
  public:
    model(void) { } 
  };

  enum result { SAT, UNSAT, UNKNOWN };

  solver(void);
  solver(options& opts);

  // Post a constraint
  // bool post(bexpr& e);

  // Solving
  result solve(void);

  // Retrieve a model
  model get_model(void); 
   
  // For incremental solving
  void level_push(void);
  void level_pop(void);
  
  solver_data* data;  
};

class solver::options {
public: 
  options(void)
  { } 

};
static const solver::options default_options = solver::options();

}

#endif
