#ifndef PHAGE_BRANCH_H
#define PHAGE_BRANCH_H
#include "engine/phage-types.h"
#include "engine/infer.h"

namespace phage {

class brancher {
public:
  virtual ~brancher(void) { }
  virtual patom_t branch(solver_data* s) = 0;
};

brancher* default_brancher(solver_data* s);

patom_t branch(solver_data* s);

}
#endif
