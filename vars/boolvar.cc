#include "engine/env.h"
#include "vars/boolvar.h"

BoolVar BVarMan::newVar(void) {
  // WARNING: This is a bit dangerous; if you
  // assign new variables after assignments have
  // been made, you may end up with segfaults.
  bvar_id id = assigns.size();
  assigns.push(TrInt(&(e->gen_trail), 0));

  return BoolVar(this, id);
}
