#include "solver/solver.h"
#include "solver/solver_data.h"

namespace phage {

typedef solver_data sdata;

solver::solver(void)
  : data(new solver_data(default_options)),
    ivar_man(data) {
   
}

solver::solver(options& _opts)
  : data(new solver_data(_opts)),
    ivar_man(data) {

}

solver_data::solver_data(const options& _opts)
    : opts(_opts) {
  new_pred(*this);
}

intvar solver::new_intvar(int64_t lb, int64_t ub) {
  return ivar_man.new_var(lb, ub);
}
  
inline bool is_bool(sdata& s, pid_t p) { return s.state.pred_is_bool(p); }

pid_t new_pred(sdata& s) {
  s.pred_callbacks.push();
  s.pred_callbacks.push();

  s.pred_queued.push(false);
  s.pred_queued.push(false);

  s.wake_queued.push(false);
  s.wake_queued.push(false);

  s.state.new_pred();
  s.persist.new_pred();
  return s.infer.new_pred();
}

bool enqueue(sdata& s, patom_t p, reason r) {
  /*
  if(is_bool(s, p.pid)) {
    NOT_YET;
//    int var = p.pid&1 ? pval_max - p.val : p.val;
    return true; 
  } else {
    if(s.state.p_vals[p.pid] < p.val) {
      if(s.state.is_inconsistent(p)) {
        // Setup conflict
        return false;
      }
      infer_info::entry e = { p.pid, s.state.p_vals[p.pid], r };
      s.infer.trail.push(e);
      s.state.p_vals[p.pid] = p.val;
    }
    return true;
  }
  */
  assert(p.pid < s.pred_queued.size());
  assert(!s.state.is_entailed(p));
  pval_t old_val = s.state.p_vals[p.pid];
  if(!s.state.post(p)) {
    // Setup conflict
    NOT_YET_WARN;
    return false;
  }
  infer_info::entry e = { p.pid, old_val, r };
  s.infer.trail.push(e);
  if(!s.pred_queued[p.pid]) {
    s.pred_queue.insert(p.pid);
    s.pred_queued[p.pid] = true;
  }
  return true;
}

// Modifies elt.watch;
inline vec<clause_head>& find_watchlist(solver_data& s, clause_elt& elt) {
  // Find the appropriate watch_node.
  if(is_bool(s, elt.atom.pid)) {
    int idx = elt.atom.pid&1 ? pval_max - elt.atom.val : elt.atom.val;
    return s.infer.bool_watches[idx];
  }

  if(elt.watch)
    return elt.watch->ws;

  patom_t p(~elt.atom);   
  watch_node* watch = s.infer.get_watch(p.pid, p.val);
  elt.watch = watch;
  return watch->ws;
}

inline bool update_watchlist(solver_data& s,
    clause_elt elt, vec<clause_head>& ws) {
  int jj = 0;
  int ii;
  for(ii = 0; ii < ws.size(); ii++) {
    clause_head ch = ws[ii];
    if(s.state.is_entailed(ch.e0)) {
      // If the clause is satisfied, just
      // copy the watch and keep going;
      ws[jj++] = ch;
      continue;
    }
    if(!ch.c) {
      // Binary clause.
      if(!enqueue(s, ch.e0, elt.atom)) {
        // Copy remaining watches and signal conflict.
        for(; ii < ws.size(); ii++)
          ws[jj++] = ws[ii];
        ws.shrink(ii-jj);
        return false;
      }
      ws[jj++] = ch;
      continue;
    }
    // Normal case: look for a new watch
    clause& c(*ch.c);
    if(c[1].atom != elt.atom) {
      assert(c[0].atom == elt.atom);
      c[0] = c[1];
    }

    if(s.state.is_entailed(c[0].atom)) {
      // If we've found something true, don't bother
      // updating the watches: just record the satisfying
      // in the head.
      c[1] = elt;
      ch.e0 = c[0].atom;
      ws[jj++] = ch;
      goto next_clause;
    }

    for(int li = 2; li < c.size(); li++) {
      if(s.state.is_entailed(c[li].atom)) {
        // As above
        c[1] = elt;
        ch.e0 = c[li].atom;
        ws[jj++] = ch;
        goto next_clause;
      }
      if(!s.state.is_inconsistent(c[li].atom)) {
        // Literal is not yet false. New watch is found.
        clause_elt new_watch = c[li];
        c[1] = new_watch;
        c[li] = elt;
        // Modifies c[1].watch in place
        vec<clause_head>& dest(find_watchlist(s, c[1]));
        dest.push(ch);
        goto next_clause;
      }
    }
    // No watches found
    c[1] = elt;
    if(!enqueue(s, c[0].atom, &c))
      return false;

next_clause:
    continue;
  }
  return true;
}

inline bool propagate_pred(solver_data& s, pid_t p) {
  if(is_bool(s, p)) {
    NOT_YET;
    return true; 
  } else {
    // Process watches
    watch_node* curr = s.infer.pred_watches[p];
    while(curr->succ) {
      watch_node* next = curr->succ;
      patom_t atom(next->atom);
      if(!s.state.is_entailed(atom))
        break;
      
      curr = next;
      if(!update_watchlist(s, ~atom, curr->ws))
        return false;
    }
    // Trail head of watches 
    // FIXME: Do it
    NOT_YET_WARN;
    s.infer.pred_watches[p] = curr;

    return true;
  }
}

// Record that the value of p has changed at the
// current decision level.
inline void touch_pred(solver_data& s, pid_t p) {
  if(!s.persist.pred_touched[p]) {
    s.persist.pred_touched[p] = true;
    s.persist.touched_preds.push(p);
  }
}

inline void wakeup_pred(solver_data& s, pid_t p) {
  assert(!is_bool(s, p)); // Handle Bool wake-up separately
  for(watch_callback call : s.pred_callbacks[p])
    call();
  s.wake_queued[p] = false;
}

// FIXME: Doesn't deal with bools at all.
bool propagate(solver_data& s) {
  // Propagate any entailed clauses
  while(!s.pred_queue.empty()) {
prop_restart:
    pid_t pi = s.pred_queue._pop();
    if(!propagate_pred(s, pi))
      return false;
    s.pred_queued[pi] = false;
    if(!s.wake_queued[pi]) {
      s.wake_queue.push(pi);
      s.wake_queued[pi] = true;
    }
  }
  
  // Fire any events for the changed predicates
  for(pid_t pi : s.wake_queue) {
    touch_pred(s, pi);
    wakeup_pred(s, pi);  
  }
  s.wake_queue.clear();

  // Process enqueued propagators
  while(!s.prop_queue.empty()) {
    propagator* p = s.prop_queue._pop();
    if(!p->propagate(s.infer.confl))
      return false; 

    // If one or more predicates were updated,
    // jump back to 
    if(!s.pred_queue.empty())
      goto prop_restart;
  }

  return true;
}

// Solving
solver::result solver::solve(void) {
  return UNKNOWN;
}

// Retrieve a model
// precondition: last call to solver::solve returned SAT
solver::model solver::get_model(void) {
  model m;
  return m;   
}
   
// For incremental solving; any constraints
// added after a push are paired with an activation
// literal.
void solver::level_push(void) {
  NOT_YET;   
}

// Drop any constraints added at the current
// context. 
void solver::level_pop(void) {
  NOT_YET; 
}

// Post a constraint
/*
bool solver::post(bexpr& e) {
  return true;
}
*/

bool add_clause(solver_data& s, vec<clause_elt>& elts) {
  int jj = 0;
  for(clause_elt e : elts) {
    if(s.state.is_entailed_l0(e.atom))
      return true;
    if(s.state.is_inconsistent_l0(e.atom))
      continue;
    elts[jj++] = e;
  }
  elts.shrink(elts.size()-jj);
  
  // False at root level
  if(elts.size() == 0)
    return false;
  // Unit at root level
  if(elts.size() == 1)
    return enqueue(s, elts[0].atom, reason()); 
  
  // Binary clause; embed the -other- literal
  // in the head;
  if(elts.size() == 2) {
    clause_head h0(elts[0].atom);
    clause_head h1(elts[1].atom);

    find_watchlist(s, elts[0]).push(h1);
    find_watchlist(s, elts[1]).push(h0); 
  } else {
    // Normal clause
    clause* c(clause_new(elts));
    // FIXME: Choose appropriate watches
    clause_head h(elts[2].atom, c);

    find_watchlist(s, elts[0]).push(h);
    find_watchlist(s, elts[1]).push(h); 
  }
  return true;
}

}
