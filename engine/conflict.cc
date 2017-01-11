#include <algorithm>
#include "solver/solver_data.h"
#include "solver/solver_debug.h"
#include "engine/conflict.h"

namespace phage {

// ex_val is the bound which must be entailed
static inline void bump_clause_act(solver_data* s, clause& cl) {
  cl.extra.act += s->learnt_act_inc;
}

static inline void bump_pred_act(solver_data* s, pid_t p) {
  // FIXME: Update order in heap, also.
  /*
  s->infer.pred_act[p] += s->pred_act_inc;
  if(s->pred_heap.inHeap(p))
    s->pred_heap.decrease(p);
  */
  /*
  unsigned int x = p>>1;
  s->infer.pred_act[x] += s->pred_act_inc;
  if(s->pred_heap.inHeap(x))
    s->pred_heap.decrease(x);
  */
}

struct cmp_clause_act {
  bool operator()(clause* x, clause* y) { return x->extra.act > y->extra.act; }
};

inline void remove_watch(watch_node* watch, clause* cl) {
  // Locate the clause_head matching cl. 
  for(clause_head& elt : watch->ws) {
    if(elt.c == cl) {
      elt = watch->ws.last();
      watch->ws.pop();
      return;
    }
  }
}

inline void detach_clause(clause* cl) {
  // At least the current watches should be cached
  if(!cl->extra.one_watch) {
    assert((*cl)[0].watch);
    remove_watch((*cl)[0].watch, cl);
  }
  assert((*cl)[1].watch);
  remove_watch((*cl)[1].watch, cl);
}

inline bool is_locked(solver_data* s, clause* c) {
  int depth = c->extra.depth;
  if(s->infer.trail.size() <= depth)
    return false;

  reason& r(s->infer.trail[depth].expl); 
  return r.kind == reason::R_Clause && r.cl == c;
}

void reduce_db(solver_data* s) {
  // Find the median of the clauses by activity
  vec<clause*>& learnts(s->infer.learnts);
  clause** mid = &learnts[s->learnt_dbmax/2];
  std::nth_element(learnts.begin(), mid, learnts.end(), cmp_clause_act());
  int shrunk_lits = 0;
  
  for(clause* c : range(mid, learnts.end())) {
    // If this clause is locked, we can't detach it
    if(is_locked(s, c)) {
      *mid = c; ++mid; 
      continue;
    }
    shrunk_lits += c->size();
    detach_clause(c);
    delete c;
  }
  int num_shrunk = learnts.end() - mid;
  s->stats.num_learnts -= num_shrunk;
  s->stats.num_learnt_lits -= shrunk_lits;
  learnts.shrink(num_shrunk);
  
  s->learnt_dbmax *= s->opts.learnt_growthrate;
}

// Pre: Conflict stuff is in 

static void clear(solver_data* s) {
  s->confl.pred_seen.clear(); 
}

// Drop a predicate from the explanation
static void remove(solver_data* s, pid_t p) {
  s->confl.pred_seen.remove(p);
  if(s->state.p_last[p] < s->confl.pred_eval[p])
    s->confl.clevel--;
}

static void add(solver_data* s, clause_elt elt) {
  assert(s->state.is_inconsistent(elt.atom));
  pid_t pid = elt.atom.pid^1;
  pval_t val = pval_max - elt.atom.val + 1;
  if(!s->confl.pred_seen.elem(pid)) {
    // Not yet in the explanation
    /*
    if(s->confl.pred_saved[pid].last_seen != s->confl.confl_num) {
      s->confl.pred_saved[pid] = { s->confl.confl_num, val };
      bump_pred_act(s, pid);
    }
    */
    if(s->confl.pred_saved[pid>>1].last_seen != s->confl.confl_num) {
      s->confl.pred_saved[pid>>1] = { s->confl.confl_num,
        pid&1 ? pval_inv(val) : val };
      bump_pred_act(s, pid);
    }

    s->confl.pred_seen.insert(pid);
    s->confl.pred_eval[pid] = val;
    s->confl.pred_hint[pid] = elt.watch;

    if(s->state.p_last[pid] < val)
      s->confl.clevel++;
  } else {
    // Check whether the atom is already entailed.
    // pval_t val = elt.atom.val;
    if(val <= s->confl.pred_eval[pid])
      return;
    
    // Check whether this changes the current-level count
    if(s->state.p_last[pid] < val
      && s->confl.pred_eval[pid] <= s->state.p_last[pid])
      s->confl.clevel++;

    s->confl.pred_eval[pid] = val;
    s->confl.pred_hint[pid] = elt.watch;
  }
  assert(s->confl.pred_seen.elem(pid));
}

std::ostream& operator<<(std::ostream& o, reason r) {
  o << "<- ";
  switch(r.kind) {
    case reason::R_Atom:
      o << r.at;
      break;
    case reason::R_Clause:
      {
        vec<clause_elt> es;
        auto it = r.cl->begin();
        o << "(" << *it << ")";
        for(++it; it != r.cl->end(); ++it)
          es.push(*it);
        o << es;
      }
      break;
    case reason::R_Thunk:
      {
        o << "{thunk}";
        break;
      }
    case reason::R_LE:
      {
        o << "{<=}";
        break;
      }
    case reason::R_NIL:
      {
        o << "true";
        break;
      }
    default:
      NOT_YET;
  }
  return o;
}

// Restore solver state to a given index in the inference trail.
static inline void bt_infer_to_pos(solver_data* s, unsigned int pos) {
  pred_state& st(s->state);
  infer_info& inf(s->infer);
  for(infer_info::entry e : rev_range(&inf.trail[pos], inf.trail.end())) {
    st.p_vals[e.pid] = e.old_val; 
  }
  inf.trail.shrink_(inf.trail.size() - pos);
}

static forceinline void add_reason(solver_data* s, unsigned int pos, pval_t ex_val, reason r) {
  switch(r.kind) {
    case reason::R_Atom:
#ifdef PROOF_LOG
      log::add_atom(*s, r.at);
#endif
      add(s, r.at);
      break;
    case reason::R_Clause:
      {
        // Skip the first literal (which we're resolving on)
        bump_clause_act(s, *r.cl);
        auto it = r.cl->begin();
        for(++it; it != r.cl->end(); ++it) {
#ifdef PROOF_LOG
          log::add_atom(*s, (*it).atom);
#endif
          add(s, *it);
        }
      }
      break;
    case reason::R_LE:
      {
        // p <= q + offset.
        patom_t at(~patom_t(r.le.p, ex_val + r.le.offset));
#ifdef PROOF_LOG
        log::add_atom(*s, at);
#endif
        add(s, at);
      }
      break;
    case reason::R_Thunk:
      {
        if(r.eth.flags) {
          // Deal with Ex_BTPRED and Ex_BTGEN
          if(r.eth.flags&expl_thunk::Ex_BTPRED) {
            bt_infer_to_pos(s, pos);
          }
          if(r.eth.flags&expl_thunk::Ex_BTGEN) {
            NOT_YET;
          }
        }
        vec<clause_elt> es;
        r.eth(ex_val, es);
        for(clause_elt e : es) {
#ifdef PROOF_LOG
          log::add_atom(*s, e.atom);
#endif
          add(s, e);
        }
      }
      break;
    case reason::R_NIL:
      break;
    default:
      NOT_YET;
  }
}

// Is the given trail entry required in the conflict?
inline bool needed(solver_data* s, infer_info::entry& entry) {
  return s->confl.pred_seen.elem(entry.pid) &&
    entry.old_val < s->confl.pred_eval[entry.pid]; 
}

inline bool l_needed(solver_data* s, persistence::pred_entry entry) {
  return s->confl.pred_seen.elem(entry.p) &&
    entry.v < s->confl.pred_eval[entry.p];
}

inline clause_elt get_clause_elt(solver_data* s, pid_t p) {
  return clause_elt(
    patom_t(p^1, pval_max - s->confl.pred_eval[p] + 1),
    s->confl.pred_hint[p]
  );
}

int compute_learnt(solver_data* s, vec<clause_elt>& confl) {
  s->confl.clevel = 0;
  s->confl.confl_num++;
  
//  std::cout << "confl:" << confl << std::endl;

  // Remember: the conflict contains things which are false.
  // The inference trail contains things which have become true.
#ifdef PROOF_LOG
  log::start_infer(*s);
#endif
  for(clause_elt e : confl) {
#ifdef PROOF_LOG
    log::add_atom(*s, e.atom);
#endif
    add(s, e);
  }
#ifdef PROOF_LOG
  log::finish_infer(*s);
#endif

  // We'll re-use confl to hold the output
  assert(s->confl.clevel > 0);
  confl.clear();
 

  // Allocate conflict for everything
  // NOTE: This should be safe, since if we're conflicting
  // there must be at least one entry on the trail.
  unsigned int pos = s->infer.trail.size()-1;
  while(!needed(s, s->infer.trail[pos])) {
    assert(pos >= 1);
    pos--;
  }

  infer_info::entry e(s->infer.trail[pos]);
  while(s->confl.clevel > 1) {
    pval_t ex_val(s->confl.pred_eval[e.pid]);
    remove(s, e.pid);
#ifdef LOG_ALL
    std::cout << " <~ {" << pos << "} " << e.expl << std::endl;
#endif
#ifdef PROOF_LOG
    // Update the hint
    if(e.expl.origin != s->log.last_hint) {
      s->log.last_hint = e.expl.origin;
      fprintf(stderr, "c %d\n", e.expl.origin);
    }
    log::start_infer(*s);
    log::add_atom(*s, patom_t { e.pid, ex_val });
#endif

    add_reason(s, pos, ex_val, e.expl); 
    
#ifdef PROOF_LOG
    log::finish_infer(*s);
#endif

    assert(pos >= 1);
    pos--;
    while(!needed(s, s->infer.trail[pos])) {
      assert(pos >= 1);
      pos--;
    }
    e = s->infer.trail[pos];
  }
  
  // We've found the 1-UIP. Now extract the nogood.

  // e contains the asserting predicate.
  confl.push(get_clause_elt(s, e.pid));
  remove(s, e.pid);

  // Identify the backtrack level and position the
  // second watch.
  int bt_level = 0;
  pos = s->persist.pred_ltrail.size();
  for(int l = s->persist.pred_ltrail_lim.size()-1; l > 0; l--) {
    // The awkwardness here is to avoid pos underflowing.
    while(pos > s->persist.pred_ltrail_lim[l]) {
      --pos;
      persistence::pred_entry e(s->persist.pred_ltrail[pos]);
      if(l_needed(s, e)) {
        // Literal would become unfixed at the previous level
        bt_level = l;
        confl.push(get_clause_elt(s, e.p));
        remove(s, e.p);
        goto level_found;
      }
    }
  }
#ifdef CHECK_STATE
  assert(bt_level < s->infer.trail_lim.size());
#endif
level_found:
  // Now push the remaining elts
  for(unsigned int p : s->confl.pred_seen)
    confl.push(get_clause_elt(s, p));
  clear(s);

#ifdef PROOF_LOG
  log::log_learnt(*s, confl);
#endif
 
  return bt_level;
}

bool confl_is_current(solver_data* s, vec<clause_elt>& confl) {
  for(clause_elt& e : confl) {
    if(!s->state.is_inconsistent_prev(e.atom))
      return true;
  }
  return false;
}

}
