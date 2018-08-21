#ifndef GEAS__MDD_H
#define GEAS__MDD_H
#include "solver/solver_data.h"
#include "utils/bitset.h"

// Packed-bit representation of MDDs.
namespace geas {
  namespace mdd {

struct mdd_info {
  mdd_info(void) { }

  vec<unsigned int> num_nodes;
  vec<unsigned int> num_edges;
  vec<unsigned int> num_vals;

  vec< vec<bitset::support_set> > val_support;
  vec< vec<bitset::support_set> > edge_HD;
  vec< vec<bitset::support_set> > edge_TL;
};

typedef int mdd_id;

mdd_id of_tuples(solver_data* s, vec< vec<int> >& tuples);
mdd_info& lookup(solver_data* s, mdd_id m);


  }
}
#endif
