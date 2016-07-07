#ifndef PHAGE_PERSIST_H
#define PHAGE_PERSIST_H

// Data structures for managing trailing and
// restoration (except the implication graph, which
// is dealt with in infer.h

namespace phage {

class solver_data;

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

  vec<bool> pred_touched;
  vec<pid_t> touched_preds;

  // For restoring prediate states
  vec<int> bvar_trail;
  vec<int> bvar_trail_lim;

  vec<pred_entry> pred_ltrail;
  vec<int> pred_ltrail_lim;

  // Temporary explanations
  // FIXME: Set up some arena stuff

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
