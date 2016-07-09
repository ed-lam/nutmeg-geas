#include "solver/solver_data.h"
#include "engine/conflict.h"

namespace phage {

// Pre: Conflict stuff is in 

static void clear(solver_data* s) {
  s->confl.pred_seen.clear(); 
}

// Drop a predicate from the explanation
static void remove(solver_data* s, pid_t p) {
  // FIXME: Handle Booleans
  s->confl.pred_seen.remove(p);
}

static void add(solver_data* s, clause_elt elt) {
  // FIXME: Handle bools
  pid_t pid = elt.atom.pid;
  if(!s->confl.pred_seen.elem(pid)) {
    // Not yet in the explanation
    s->confl.pred_seen.insert(pid);
    s->confl.pred_eval[pid] = elt.atom.val;
    s->confl.pred_hint[pid] = elt.watch;

    if(s->state.p_last[pid] < elt.atom.val)
      s->confl.clevel++;
  } else {
    // Check whether the atom is already entailed.
    pval_t val = elt.atom.val;
    if(val <= s->confl.pred_eval[pid])
      return;
    
    // Check whether this changes the current-level count
    if(s->state.p_last[pid] < val
      && s->confl.pred_eval[pid] <= s->state.p_last[pid])
      s->confl.clevel++;

    s->confl.pred_eval[pid] = elt.atom.val;
  }
  assert(s->confl.pred_seen.elem(pid));
}

static void add_reason(solver_data* s, reason r) {
  switch(r.kind) {
    case reason::R_Atom:
      add(s, r.at);
      break;
    case reason::R_Clause:
      {
        // Skip the first literal (which we're resolving on)
        auto it = r.cl->begin();
        for(++it; it != r.cl->end(); ++it)
          add(s, *it);
      }
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
    patom_t(p, s->confl.pred_eval[p]),
    s->confl.pred_hint[p]
  );
}

int compute_learnt(solver_data* s, vec<clause_elt>& confl) {
  for(clause_elt e : confl)
    add(s, e);

  // We'll re-use confl to hold the output
  confl.clear();
 
  assert(s->confl.clevel > 0);

  // Allocate conflict for everything

  unsigned int pos = s->infer.trail.size()-1;
  while(!needed(s, s->infer.trail[pos]))
    pos--;

  infer_info::entry e(s->infer.trail[pos]);
  while(s->confl.clevel > 1) {
    remove(s, e.pid);
    add_reason(s, e.expl); 

    pos--;
    while(!needed(s, s->infer.trail[pos]))
      pos--;
    e = s->infer.trail[pos];
  }
  
  // We've found the 1-UIP. Now extract the nogood.

  // e contains the asserting predicate.
  confl.push(get_clause_elt(s, e.pid));
  remove(s, e.pid);

  // Identify the backtrack level and position the
  // second watch.
  int bt_level = 0;
  pos = s->persist.pred_ltrail.size()-1;
  for(int l = s->persist.pred_ltrail_lim.size()-1; l > 0; l--) {
    for(; pos > s->persist.pred_ltrail_lim[l]; pos--) {
      persistence::pred_entry e(s->persist.pred_ltrail[pos]);
      if(l_needed(s, e)) {
        // Literal would become unfixed at the previous level
        bt_level = l;
        confl.push(get_clause_elt(s, e.p));
        goto level_found;
      }
    }
  }
level_found:
  // Now push the remaining elts
  for(unsigned int p : s->confl.pred_seen)
    confl.push(get_clause_elt(s, p));
  clear(s); 
 
  return bt_level;
}

}
