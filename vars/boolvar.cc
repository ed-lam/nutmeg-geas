#include "engine/env.h"
#include "vars/boolvar.h"

BoolVar BVarMan::newVar(void) {
  // WARNING: This is a bit dangerous; if you
  // assign new variables after assignments have
  // been made, you may end up with segfaults.
  atom_tok id = new_atom_tok();
  assert(id == assigns.size());
  assigns.push(TrInt(&(e->gen_trail), 0));

  return BoolVar(this, id);
}
