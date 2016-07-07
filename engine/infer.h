#ifndef PHAGE_INFER__H
#define PHAGE_INFER__H
#include <map>
#include <vector>

#include "mtl/int-triemap.h"
#include "infer-types.h"

namespace phage {

class infer_info {
public:
  // Predicates 0 and 1 are placeholders, and always
  // exist.
  infer_info(void) {
    // Done by solver_data constructor
    // new_pred();
  }

  // Predicates should only be added in pairs.
  pid_t new_pred(void) {
    pid_t p = new_half_pred();
    new_half_pred();
    return p;
  }

  void growTo(int sz) {
    while(watch_maps.size() <= sz)
      new_pred();
  }

protected:
  pid_t new_half_pred(void) {
    pid_t pid = watch_maps.size();
    // Create the root watch-node
    watch_node* w(new watch_node); 
    w->atom = patom_t(pid, 0);
    pred_watches.push(w);
    pred_watch_heads.push(w);

    watch_maps.push();
    watch_maps.last().add(0, w);
    return pid;
  }

public:
  // Find the appropriate watch for an atom.
  watch_node* get_watch(pid_t p, pval_t val) {
    watch_map::iterator it = watch_maps[p].find(val);
    if(it != watch_maps[p].end()) 
      return (*it).value;
    watch_node* w(new watch_node);
    w->atom = patom_t(p, val);

    // This repeats the lookup performed by
    // find. Modify avoid this.
    it = watch_maps[p].add(val, w);
    --it;
    watch_node* pred = (*it).value;
    w->succ = pred->succ;
    pred->succ = w;
    return w;
  }

  typedef struct {
    pid_t pid;
    pval_t old_val;
    reason expl;
  } entry;
  
  // Watches and learnts for Bools
  vec< vec<clause_head> > bool_watches;

  // Same for predicates
  vec<watch_map> watch_maps; // (pid_t -> pval_t -> watch_node*)
  vec<watch_node*> pred_watches;
  vec<watch_node*> pred_watch_heads; // Watches for [| pid >= min_val |].

  // Inference graph and backtracking
  vec<int> trail_lim;
  vec<entry> trail;

  // Temporary storage for the conflict
  vec<clause_elt> confl;  

  vec<clause*> clauses;
  vec<clause*> learnts;
};

}
#endif
