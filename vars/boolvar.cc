#include "engine/env.h"
#include "vars/boolvar.h"

BoolVar BVarMan::newVar(void) {
  atom_tok id = new_atom_tok();
  assert(id == assigns.size());
  assigns.push(l_Undef);
  level.push(0);
  ws.push();
  ws.push();

  return BoolVar(this, id);
}
