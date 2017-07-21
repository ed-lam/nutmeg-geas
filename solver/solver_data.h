#ifndef PHAGE_SOLVER_IMPL__H
#define PHAGE_SOLVER_IMPL__H
#include <signal.h>
#include "mtl/Vec.h"
#include "mtl/Heap.h"
#include "mtl/Queue.h"
#include "engine/phage-types.h"
#include "engine/state.h"
#include "engine/infer.h"
#include "engine/persist.h"
#include "engine/propagator.h"
#include "engine/conflict.h"

#include "engine/logging.h"

// #include "solver/solver.h"
#include "solver/branch.h"
#include "solver/options.h"
#include "solver/stats.h"
#include "solver/model.h"

namespace phage {

struct act_cmp {
  bool operator()(int i, int j) { return act[i] > act[j]; }; 
  vec<double>& act;
};

enum ConflKind { C_Infer, C_Assump };
struct confl_info { ConflKind kind; int assump_idx; };

// So we can easily introduce new variable types
struct manager_t {
  void* ptr;  
  void (*destroy)(void*);
};
typedef unsigned int man_id_t;

enum PredFlags { PR_DEFAULT = 0, PR_NOBRANCH = 1 };

class solver_data {
public:
  solver_data(const options& _opts);
  ~solver_data(void);

  model incumbent;

  options opts;
  statistics stats;
   
  pred_state state;
  infer_info infer;
  persistence persist;
  conflict_info confl;

  proof_log log;

  vec< vec<watch_callback> > pred_callbacks;
  // Used for dynamic idempotence
  // handling
  vec<void*> pred_origin;
  void* active_prop;

  Queue<pid_t> pred_queue;
  vec<bool> pred_queued;

  vec<pid_t> wake_queue;
  vec<bool> wake_queued;
  vec<pval_t> wake_vals;
  
  Queue<propagator*> prop_queue;

  vec<propagator*> propagators;
  vec<brancher*> branchers;
  brancher* last_branch;

  Heap<act_cmp> pred_heap;

  vec<patom_t> assumptions;
  vec<int> assump_level;
  int assump_end;

  vec<int> assump_ctx_lim;

  // Initialization thunks for
  // lazily added predicates.
  // struct pinit_data { int pi; pred_init init; };
  vec<pinit_data> initializers;
  unsigned int init_end;

  // Callbacks for various events
  vec<event_callback> on_pred;
  vec<event_callback> on_branch;
  vec<event_callback> on_solution;

  vec<bool> polarity;

  confl_info last_confl;

  double learnt_act_inc;
  double pred_act_inc;
  int learnt_dbmax;
  int restart_limit;

  volatile sig_atomic_t abort_solve; 

  vec<manager_t> managers;
};

man_id_t register_manager(void* (*create)(solver_data* s), void (*destroy)(void*));

inline int num_preds(solver_data* s) { return s->pred_callbacks.size(); }

pid_t new_pred(solver_data& s, pval_t lb = pval_min, pval_t ub = pval_max, unsigned char pred_flags = PR_DEFAULT);
pid_t new_pred(solver_data& s, pred_init init_lb, pred_init init_ub, unsigned char pred_flags = PR_DEFAULT);

patom_t new_bool(solver_data& s);
patom_t new_bool(solver_data& s, pred_init init_l, pred_init init_u);

inline void queue_pred(solver_data* s, pid_t p) {
  if(!s->pred_queued[p]) {
    s->pred_queue.insert(p);
    s->pred_queued[p] = true;
  }
}

inline pval_t pred_val(solver_data* s, pid_t p) { return s->state.p_vals[p]; }
inline bool pred_fixed(solver_data* s, pid_t p) { return pval_max - pred_val(s, p) == pred_val(s, p^1); }

inline pval_t pred_lb(solver_data* s, pid_t p) { return s->state.p_vals[p]; }
inline pval_t pred_ub(solver_data* s, pid_t p) { return pval_inv(s->state.p_vals[p^1]); }

inline pval_t pred_lb_prev(solver_data* s, pid_t p) { return s->state.p_last[p]; }
inline pval_t pred_ub_prev(solver_data* s, pid_t p) { return pval_inv(s->state.p_last[p^1]); }

bool propagate(solver_data& s);
// bool enqueue(solver_data& s, patom_t p, reason r);
bool _enqueue(solver_data& s, patom_t p, reason r);
inline bool enqueue(solver_data& s, patom_t p, reason r) {
  if(s.state.is_entailed(p))
    return true;
  return _enqueue(s, p, r);
}

// Warning: Modifies elts in place.
bool add_clause(solver_data& s, vec<clause_elt>& elts);
// For adding at non-0 decision level
bool add_clause_(solver_data& s, vec<clause_elt>& elts);

void attach(solver_data* s, patom_t p, const watch_callback& c);

template<typename... Ts>
bool add_clause(solver_data* s, patom_t e, Ts... args) {
  vec<clause_elt> elts;
  elts.push(e);
  vec_push(elts, args...);
  return add_clause(*s, elts);  
}

template<typename... Ts>
bool add_clause_(solver_data* s, patom_t e, Ts... args) {
  vec<clause_elt> elts;
  elts.push(e);
  vec_push(elts, args...);
  return add_clause_(*s, elts);  
}


// For debugging
std::ostream& operator<<(std::ostream& o, const patom_t& at);

std::ostream& operator<<(std::ostream& o, const clause_elt& e);

}
#endif
