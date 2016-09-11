#include "mtl/Vec.h"
#include "utils/defs.h"

#include "c/atom.h"
#include "c/phage.h"
#include "c/builtins.h"

#include "c/marshal.h"

#include "solver/solver_data.h"

#ifdef __cplusplus
extern "C" {
#endif

int clause(solver s, atom* cl, int sz) {
  vec<phage::clause_elt> elts;
  for(int ii : irange(sz))
    elts.push(get_atom(cl[ii]));
  return add_clause(*get_solver(s)->data, elts);
}

// These are half-reified.
// For strict versions, call with r = at_True
int linear_le(solver s, atom r, linterm* ts, int sz) {
  assert(0 && "Implement");
}

int int_mul(solver s, atom r, intvar z, intvar x, intvar y) {
  assert(0 && "Implement");
}

int int_abs(solver s, atom r, intvar z, intvar x) {
  assert(0 && "Implement");
  return 0;
}

#ifdef __cplusplus
}
#endif
