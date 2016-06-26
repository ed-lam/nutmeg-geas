#ifndef PHAGE_INFER_TYPES__H
#define PHAGE_INFER_TYPES__H
/* Types for the inference engine */
#include <stdint.h>
#include <vector>
#include <mtl/Vec.h>

#include "utils/defs.h"
#include "engine/phage-types.h"

namespace phage {

class watch_node;

class clause_elt {
public:
  clause_elt(patom_t _at)
    : atom(_at), watch(nullptr)
  { }
  patom_t atom;
  // We cache the appropriate watch-list
  watch_node* watch;
};

class clause {
public:
  template<class T> clause(T& elts) {
    sz = 0;
    for(clause_elt e : elts)
      data[sz++] = e;
  }
  int size(void) const { return sz; }
  
  clause_elt& operator[](int ii) { return data[ii]; }
  clause_elt* begin(void) { return &(data[0]); }
  clause_elt* end(void) { return &(data[sz]); }
protected:
  int sz;
  clause_elt data[0];
};

// If c == NULL, the clause is binary -- e0 is the 'other' literal
class clause_head {
public: 
  patom_t e0; // We can stop if e0 is true.
  clause* c;
};

// Watches for a given atom.
// Maintains a pointer to the next watch.
class watch_node {
public:
  patom_t atom; 
  watch_node* succ;  
  vec<clause_head> ws;
};

// For a given pid_t, map values to the corresponding
// watches.
typedef std::map<pval_t, watch_node*> watch_map;

}

#endif
