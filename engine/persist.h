#ifndef PHAGE_PERSIST_H
#define PHAGE_PERSIST_H

// Data structures for managing trailing and
// restoration (except the implication graph, which
// is dealt with in infer.h
#include "engine/phage-types.h"
#include "engine/infer-types.h"

namespace phage {

class solver_data;

class expl_builder {
public:
  expl_builder(clause* _c)
    : c(_c), hd(&(*c)[1]) { }

  void push(const clause_elt& e) { *hd = e; ++hd; }    
  clause* operator*(void) { c->sz = hd - c->begin(); return c; }

  clause* c;
  clause_elt* hd;
};

class persistence {
public:
  typedef struct {
    pid_t p;
    pval_t v;
  } pred_entry;

  typedef struct {
    void* ptr;
    char sz;
    uint64_t val;
  } data_entry;
  
  void new_pred(void) {
    pred_touched.push(false);
    pred_touched.push(false);
  }

  unsigned int level(void) const {
    // All the trail_lims should have the same size
    return pred_ltrail_lim.size();
  }

  void root_simplify(void) {
    for(pid_t p : touched_preds)
      pred_touched[p] = false;
    touched_preds.clear();
    bvar_trail.clear();
    bvar_trail_lim.clear();
    pred_ltrail.clear();
    pred_ltrail_lim.clear();
    data_trail.clear();
    dtrail_lim.clear();
  }

  clause* alloc_expl(unsigned int sz) {
    clause* c = alloc_clause_mem(sz);
    expl_trail.push(c);
    return c;
  }

  template<class... Es>
  clause* create_expl(Es... es) {
    clause* c = alloc_expl(1 + sizeof...(es));
    clause_elt* dest = &(*c)[1];
    ptr_push(dest, es...);
    c->sz = 1 + sizeof...(es);
    return c;
  }

  vec<bool> pred_touched;
  vec<pid_t> touched_preds;

  // For restoring prediate states
  vec<int> bvar_trail;
  vec<int> bvar_trail_lim;

  vec<pred_entry> pred_ltrail;
  vec<int> pred_ltrail_lim;

  // Temporary explanations
  vec<clause*> expl_trail;
  vec<int> expl_trail_lim;

  // Trail for other data
  vec<data_entry> data_trail;
  vec<int> dtrail_lim;
};

void push_level(solver_data* s);
void bt_to_level(solver_data* s, unsigned int l);

template<class T>
inline void trail_push(persistence& p, T& elt) {
  static_assert(sizeof(T) == 1 || sizeof(T) == 2 || sizeof(T) == 4 || sizeof(T) == 8,
    "sizeof(T) must be 2^k, k <- [0, 3]");
  persistence::data_entry e = { (void*) &elt, sizeof(T), (uint64_t) elt };
  p.data_trail.push(e); 
}

template<class T>
inline void trail_change(persistence& p, T& elt, T val) {
  trail_push(p, elt);      
  elt = val;
}


}

#endif
