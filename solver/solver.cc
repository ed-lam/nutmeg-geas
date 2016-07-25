#include <iostream>
#include "solver/solver.h"
#include "solver/solver_data.h"
#include "engine/conflict.h"

namespace phage {

typedef solver_data sdata;

solver::solver(void)
  : data(new solver_data(default_options)),
    ivar_man(data) {
   
}

solver::~solver(void) {
  // Free propagators
  delete data;
}

solver::solver(options& _opts)
  : data(new solver_data(_opts)),
    ivar_man(data) {

}

solver_data::solver_data(const options& _opts)
    : opts(_opts), last_branch(default_brancher(this)) {
  new_pred(*this);
}

solver_data::~solver_data(void) {
  for(propagator* p : propagators)
    delete p;
  for(brancher* b : branchers)
    delete b;
  assert(last_branch);
  delete last_branch;
}

intvar solver::new_intvar(int64_t lb, int64_t ub) {
  return ivar_man.new_var(lb, ub);
}

// For debugging
std::ostream& operator<<(std::ostream& o, const patom_t& at) {
  if(at.pid&1) {
    o << "p" << (at.pid>>1) << " <= " << intvar_base::to_int(pval_max - at.val);
  } else {
    o << "p" << (at.pid>>1) << " >= " << intvar_base::to_int(at.val);
  }
  return o;
}
std::ostream& operator<<(std::ostream& o, const clause_elt& e) {
  o << e.atom;
  return o;
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
  s.confl.new_pred();
  return s.infer.new_pred();
}

void set_confl(sdata& s, patom_t p, reason r, vec<clause_elt>& confl) {
  confl.clear();
  switch(r.kind) {
    case reason::R_Atom:
      confl.push(p);
      confl.push(r.at);
      break;
    case reason::R_Clause:
      for(clause_elt e : *r.cl)
        confl.push(e);
       break;
     default:
       NOT_YET;
  }
}

bool enqueue(sdata& s, patom_t p, reason r) {
  std::cout << "|- " << p << std::endl;
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
    set_confl(s, p, r, s.infer.confl); 
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
      // updating the watches: just record the satisfying atom
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
    ws[jj++] = ch;
    if(!enqueue(s, c[0].atom, &c)) {
      for(ii++; ii < ws.size(); ii++)
        ws[jj++] = ws[ii];
      return false;
    }

next_clause:
    continue;
  }
  ws.shrink(ws.size() - jj);
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
      if(!update_watchlist(s, ~atom, curr->ws)) {
        return false;
      }
    }
    // Trail head of watches 
    trail_change(s.persist, s.infer.pred_watches[p], curr);

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
    p->cleanup();

    // If one or more predicates were updated,
    // jump back to 
    if(!s.pred_queue.empty())
      goto prop_restart;
  } 
  return true;
}

inline int decision_level(sdata& s) {
  return s.infer.trail_lim.size();
}

inline void add_learnt(solver_data* s, vec<clause_elt>& learnt) {
  // Allocate the clause
  WARN("Collection of learnt clauses not yet implemented.");

  // Construct the clause
  int jj = 0;
  for(clause_elt e : learnt) {
    // Remove anything dead at l0.
    if(s->state.is_inconsistent_l0(e.atom))
      continue;
    learnt[jj++] = e;
  }
  learnt.shrink(learnt.size()-jj);
  
  // Unit at root level
  if(learnt.size() == 1) {
    enqueue(*s, learnt[0].atom, reason()); 
    return;
  }
  
  // Binary clause; embed the -other- literal
  // in the head;
  if(learnt.size() == 2) {
    // Add the two watches
    clause_head h0(learnt[0].atom);
    clause_head h1(learnt[1].atom);

    find_watchlist(*s, learnt[0]).push(h1);
    find_watchlist(*s, learnt[1]).push(h0); 
    enqueue(*s, learnt[0].atom, learnt[1].atom);
  } else {
    // Normal clause
    clause* c(clause_new(learnt));
    // Assumption:
    // learnt[0] is the asserting literal;
    // learnt[1] is at the current level
    clause_head h(learnt[2].atom, c);

    find_watchlist(*s, learnt[0]).push(h);
    find_watchlist(*s, learnt[1]).push(h); 
    enqueue(*s, learnt[0].atom, c);
  }
}

// Remove c from its watch lists.
inline void detach_watch(vec<clause_head>& ws, clause* c) {
  for(clause_head& w : ws) {
    if(w.c == c) {
      w = ws.last();
      ws.pop();
      return;
    }
  }
}

inline void replace_watch(vec<clause_head>& ws, clause* c, clause_head h) {
  for(clause_head& w : ws) {
    if(w.c == c) {
      w = h;
      return;
    }
  }
}

inline void detach_clause(solver_data& s, clause* c) {
  // We care about the watches for 
  detach_watch(find_watchlist(s, (*c)[0]), c);
  detach_watch(find_watchlist(s, (*c)[1]), c);
}

inline clause** simplify_clause(solver_data& s, clause* c, clause** dest) {
  clause_elt* ej = c->begin();
  for(clause_elt e : *c) {
    if(s.state.is_entailed_l0(e.atom)) {
      // Clause is satisfied at the root; remove it.
      detach_clause(s, c);
      delete c; 
      return dest;
    }
    if(!s.state.is_inconsistent_l0(e.atom)) {
      // Literal may become true; keep it.
      *ej = e; ++ej;
    }
  }
  c->sz = ej - c->begin();
  assert(c->sz >= 2);

  if(c->sz == 2) {
    // c has become a binary clause.
    // Inline the clause body, and free the clause.
    replace_watch(find_watchlist(s, (*c)[0]), c, (*c)[1].atom);
    replace_watch(find_watchlist(s, (*c)[1]), c, (*c)[0].atom);
    delete c;
    return dest;
  }

  *dest = c; ++dest;
  return dest;
}

// Precondition: propagate should have been run to fixpoint,
// and we're at decision level 0.
inline void simplify_at_root(solver_data& s) {
  // Update predicate values, simplify clauses
  // and clear trails.
  for(int pi = 0; pi < s.pred_callbacks.size(); pi++) {
    s.state.p_last[pi] = s.state.p_vals[pi];    
    s.state.p_root[pi] = s.state.p_vals[pi];
    
    // Do garbage collection on the watch_node*-s.
    while(s.infer.pred_watch_heads[pi] != s.infer.pred_watches[pi]) {
      watch_node* w = s.infer.pred_watch_heads[pi];
      s.infer.pred_watch_heads[pi] = w->succ;
      s.infer.watch_maps[pi].rem(w->atom.val);
      delete w;
    }
    // Now that entailed watches are deleted, we're committed
    // to simplifying all the clauses.
  }

  // Watches may be invalidated when a clause is
  // deleted because it is satisfied at the root.
  // This is dealt with in cimplify_clause.
  clause** cj = s.infer.clauses.begin();
  for(clause* c : s.infer.clauses) {
    cj = simplify_clause(s, c, cj); 
  }
  s.infer.clauses.shrink_(s.infer.clauses.end() - cj);

  clause** lj = s.infer.learnts.begin();
  for(clause* c : s.infer.learnts) {
    lj = simplify_clause(s, c, lj);
  }
  s.infer.learnts.shrink_(s.infer.learnts.end() - lj);

  for(propagator* p : s.propagators)
    p->root_simplify();
  
  // Now reset all persistence stuff. 
  s.infer.root_simplify();
  s.persist.root_simplify();

  return;
}

// Solving
solver::result solver::solve(void) {
  // Top-level failure
  sdata& s(*data);
  while(true) {
    if(!propagate(s)) {
      std::cout << "Conflict: " << s.infer.confl << std::endl;
      if(decision_level(s) == 0)
        return UNSAT;
        
      // Conflict
      int bt_level = compute_learnt(&s, s.infer.confl);
      bt_to_level(&s, bt_level);
      add_learnt(&s, s.infer.confl);
      continue;
    }

    if(decision_level(s) == 0)
      simplify_at_root(s);

    patom_t dec = branch(&s);
    if(dec == at_Undef)
      return SAT;

    assert(!s.state.is_entailed(dec));
    assert(!s.state.is_inconsistent(dec));
    std::cout << "?> " << dec << std::endl;

    push_level(&s);
    enqueue(s, dec, reason());
  }

  return SAT;
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

// Add a clause at the root level.
bool add_clause(solver_data& s, vec<clause_elt>& elts) {
  int jj = 0;
  for(clause_elt e : elts) {
    if(s.state.is_entailed(e.atom))
      return true;
    if(s.state.is_inconsistent(e.atom))
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
    // Any two watches should be fine
    clause_head h(elts[2].atom, c);

    find_watchlist(s, elts[0]).push(h);
    find_watchlist(s, elts[1]).push(h); 
  }
  return true;
}

// Add a clause, but not necessarily at the root level.
bool add_clause_(solver_data& s, vec<clause_elt>& elts) {
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
