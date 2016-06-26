#ifndef PHAGE_INFER__H
#define PHAGE_INFER__H
#include <map>
#include <vector>

#include "infer-types.h"
#if 0
#include "mtl/Vec.h"
#include "mtl/Queue.h"

/*
 * Core inference engine
 */

typedef struct {
  val_t lb;
  val_t ub;
} bounds_data;

// Bounds atom is <=.
typedef struct {
  unsigned int pid: 31;
  unsigned int is_neg: 1;
  val_t val;
} lwatch;

class clause {
 public:
  template<class T>
    clause(T& ps)
    : sz(ps.size())
    {
      unsigned int idx = 0;
      for(lwatch l : ps)
        data[idx++] = l;
    }

  lwatch* begin(void) { return &(data[0]); }
  lwatch* end(void) { return &(data[sz]); }

  lwatch& operator[](unsigned int idx) { return data[idx]; }

  unsigned int sz;
  lwatch data[0];
};

template<class T>
clause* clause_new(T& ps)
{
  void* mem(malloc(sizeof(clause) + ps.size()*sizeof(lwatch)));
  return new (mem) clause(ps);
}

typedef struct {
  lwatch elt0;
  clause* body;
} watch_elt;

class lwatch_node {
 public:
  lwatch_node(void)
    : pred_idx(-1), succ_idx(-1)
  { }
  val_t val;
  unsigned int pred_idx;
  unsigned int succ_idx;
  vec<watch_elt> ws;
};

// FIXME: Replace with something lighter-weight
typedef std::map<uint64_t, unsigned int> lwatch_map;

class Infer_state {
 public:
  lbool value(lwatch l) const {
    const bounds_data& b(bounds[l.pid]);
    if(b.ub <= l.val)
      return l.is_neg ? l_False : l_True;
    if(l.val < b.lb)
      return l.is_neg ? l_True : l_False;
    return l_Undef;
  }
  
  std::vector<lwatch_map> pred_map; // [pred_id -> { val -> idx } ]
  vec< vec<lwatch_node> > pred_watches;
  vec<unsigned int> lwatch_idx;

  vec<bounds_data> bounds;
};

// Triggers are activated whenever a predicate bound changes.
// They manage the interpretation of atoms, and waking 
class Trigger {
public:
  typedef int64_t cookie_t;
  virtual bool callback(cookie_t, val_t) = 0;
};

// Env gives access to the data
// and inference trail.
template<class Env>
class Infer {
 public:
  Infer(Env& _env)
    : env(_env)
  { }

  /* Propagation:
   * We need three kinds of information:
   * - The trail of bound changes (both from clauses and propagators)
   * - Queue of predicates with changed bounds (which may require finding
   *   new watches).
   * - Queue of predicates which may cause propagators to wake. */
  bool propagate(void)
  {
    while(!watch_pqueue.empty() || !prop_queue.empty()) {
      while(!watch_pqueue.empty()) {
        pred_id pi(watch_pqueue._pop());
        watch_queued[pi] = false;

        // Check clauses
        vec<lwatch_node>& wnodes(state.pred_watches[pi]);
        int lwatch_idx = state.lwatch_idx[pi];

        int lwatch_next = wnodes[lwatch_idx].succ_idx;
        // GKG: Double-check that signs match here
        if(pi&1) { // lb change, watches on [|x <= k|].
          val_t lim = state.bounds[pi>>1].lb;
          while(wnodes[lwatch_next].val < lim) {
            vec<watch_elt>& ws(wnodes[lwatch_next].ws);
            // Process clauses
          }
        } else { // ub change, watches on [|x > k|]
          val_t lim = state.bounds[pi>>1].ub;
          while(lim <= wnodes[lwatch_next].val) {
            vec<watch_elt>& ws(wnodes[lwatch_next].ws);
            // Process clauses
          }
        }
      }

      while(!trigger_pqueue.empty()) {
        // Notify triggers to wake-up propagators
        pred_id pi(trigger_pqueue._pop());
        trigger_queued[pi] = false;
      }

      while(!prop_queue.empty()) {
        unsigned int prop_id(prop_queue._pop());
        prop_queued[prop_id] = false;

        
      }
    }
  }
  
  // FIXME: Deal with explanations
  bool enqueue(alit l, void* r)
  {
    infer_trail.push(l);
    return true;
  }

  unsigned int infer_qhead;
  vec<alit> infer_trail;
  
  // Which predicates may have invalidated watches?
  Queue<int> watch_pqueue;
  vec<bool> watch_queued;

  // Which predicates may wake clauses?
  Queue<int> trigger_pqueue;
  vec<bool> trigger_queued;

  // Which propagators need running?
  Queue<int> prop_queue;
  vec<bool> prop_queued;
  
  Infer_state state;
  Env& env;
};
#endif

namespace phage {

class reason {
public:
  reason(void) { }
  // Stub
};

class infer_info {
public:
  infer_info(void) { }

  typedef struct {
    pid_t pi;
    pval_t old_val;
    reason expl;
  } entry;
  
  // Watches and learnts for Bools
  vec< vec<clause_head> > bool_watches;
  vec<bool> bool_seen;

  // Same for predicates
  std::vector<watch_map> watch_maps; // (pid_t -> pval_t -> watch_node*)
  vec<watch_node*> pred_watches;
  vec<watch_node*> pred_watch_heads; // Watches for [| pid >= min_val |].

  vec<bool> pred_seen; // Actually needs to be a sparse-set
  vec<pval_t> pred_seen_val;

  // Inference graph and backtracking
  vec<int> trail_lim; 
  vec<entry> trail;

  // Temporary storage for the conflict
  vec<clause_elt> confl;  
};

}
#endif
