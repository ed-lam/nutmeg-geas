#ifndef PHAGE__FLOW_CSTS_H
#define PHAGE__FLOW_CSTS_H
// Header for flow constraints
#include "vars/intvar.h"

// 0-1 flow.
namespace phage {

struct bflow {
  int src;
  int sink;
  patom_t at;    
};

bool bipartite_flow(solver_data* s, vec<int>& srcs, vec<int>& sinks, vec<bflow>& flows);

bool bipartite_flow(solver_data* s, vec<intvar>& srcs, vec<intvar>& sinks, vec<bflow>& flows);

// Integer flows
/*
struct iflow {
  int src;
  int dest;
  intvar flow; 
};
*/

}
#endif
