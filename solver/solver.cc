#include <iostream>
#include "solver/solver.h"
#include "solver/solver_data.h"
#include "solver/solver_debug.h"
#include "engine/conflict.h"


namespace phage {

pval_t patom_t::val_max = pval_max;

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
    : opts(_opts),
      // active_prop(nullptr),
      last_branch(default_brancher(this)), 
      pred_heap(act_cmp { infer.pred_act }),
      // Dynamic parameters
      learnt_act_inc(opts.learnt_act_inc),
      pred_act_inc(opts.pred_act_inc),
      learnt_dbmax(opts.learnt_dbmax) {
  new_pred(*this, 0, 0);
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

patom_t solver::new_boolvar(void) { return new_bool(*data); }

// For debugging
std::ostream& operator<<(std::ostream& o, const patom_t& at) {
  if(at.pid&1) {
    o << "p" << (at.pid>>1) << " <= " << to_int(pval_max - at.val);
  } else {
    o << "p" << (at.pid>>1) << " >= " << to_int(at.val);
  }
  return o;
}
std::ostream& operator<<(std::ostream& o, const clause_elt& e) {
  o << e.atom;
  return o;
}


// inline bool is_bool(sdata& s, pid_t p) { return s.state.pred_is_bool(p); }
// inline bool is_bool(sdata& s, pid_t p) { return false; }

inline int decision_level(sdata& s) {
  return s.infer.trail_lim.size();
}

pid_t alloc_pred(sdata& s, pval_t lb, pval_t ub) {
  s.pred_callbacks.push();
  s.pred_callbacks.push();

  s.pred_queued.push(false);
  s.pred_queued.push(false);

  // s.pred_origin.push(nullptr);
  // s.pred_origin.push(nullptr);
    
  s.wake_queued.push(false);
  s.wake_queued.push(false);

  s.state.new_pred(lb, ub);
  s.persist.new_pred();
  s.confl.new_pred();
  pid_t pi = s.infer.new_pred();

  s.pred_heap.insert(pi);
  s.pred_heap.insert(pi+1);
  
  return pi;  
}

pid_t new_pred(sdata& s, pval_t lb, pval_t ub) {
  assert(decision_level(s) == 0);
  pid_t p = alloc_pred(s, lb, ub);
  // s.state.init_end = s.state.initializers.size();
  return p;
}

void initialize(pid_t p, pred_init init, vec<pval_t>& vals) {
  pred_init::prange_t r(init(vals));
  vals[p] = r[0];
  vals[p+1] = r[1];
}

pid_t new_pred(sdata& s, pred_init init) {
  pred_init::prange_t r0(init(s.state.p_root)); 

  pid_t p = alloc_pred(s, r0[0], r0[1]);
  // Set up the prev and current values
  // Root values are set up during allocation
  initialize(p, init, s.state.p_last);
  initialize(p, init, s.state.p_vals);

  if(decision_level(s) > 0)
    s.state.initializers.push(pinit_data {p>>1, init} ); 
//  s.state.initializers[p>>1] = init;

  return p;
}

pred_init::prange_t init_bool(void* ptr, int eid, vec<pval_t>& vals) {
  // return pred_init::prange_t { {0, pval_max - 1} };
  return pred_init::prange_t { {from_int(0), pval_max - from_int(1)} };
}

patom_t new_bool(sdata& s, pred_init init) {
  pid_t pi(new_pred(s, init));
  return patom_t(pi, from_int(1));
}

patom_t new_bool(sdata& s) {
  return new_bool(s, pred_init(init_bool, nullptr, 0));
}

void set_confl(sdata& s, patom_t p, reason r, vec<clause_elt>& confl) {
  confl.clear();

  confl.push(p);
  switch(r.kind) {
    case reason::R_Atom:
      confl.push(r.at);
      break;
    case reason::R_Clause:
      for(clause_elt e : r.cl->tail())
        confl.push(e);
       break;
     case reason::R_Thunk:
     {
      // pval_t fail_val = pval_max - s.state.p_vals[p.pid^1] + 1;
      pval_t fail_val = p.val;
      assert(fail_val <= p.val);
      r.eth(fail_val, confl);
      break;
     }
     default:
       NOT_YET;
  }
}

inline bool is_entailed(sdata& s, patom_t p) { return s.state.is_entailed(p); }
inline bool is_inconsistent(sdata& s, patom_t p) { return s.state.is_inconsistent(p); }

bool solver::post(patom_t p) {
  if(decision_level(*data) > 0)
    bt_to_level(data, 0); 
  if(is_inconsistent(*data, p))
    return false;
  return enqueue(*data, p, reason());
}

bool apply_assumps(solver_data& s) {
  /*
  int idx = s.assump_end; 
  for(; idx < s.assumptions.size(); idx++) {
    patom_t at(s.assumptions[idx]); 
    s.assump_level[idx] = decision_level(s);

    if(is_entailed(s, at))
      continue;
    if(is_inconsistent(s, at))
      return false;

    
  }
  */
  return true;
}

bool solver::assume(patom_t p) {
  /*
  data->assumptions.push(p);
  if(data->state.is_entailed(p))
    return true;

  push_level(&s);
  if(!enqueue(*data, p, reason()))
    return false;
  trail_change(data->persist, data->assump_start, assumptions.size());
  return propagate(*data);
  */
  return true;
}

void solver::retract(void) {
  return; 
}

void solver::clear_assumptions(void) {
  if(decision_level(*data) > 0)
    bt_to_level(data, 0);
  data->assumptions.clear();
  data->assump_level.clear();
  data->assump_end = 0;
}

bool enqueue(sdata& s, patom_t p, reason r) {
#ifdef LOG_ALL
  std::cout << "|- " << p << std::endl;
#endif

  assert(p.pid < s.pred_queued.size());
  // assert(!s.state.is_entailed(p));
  if(s.state.is_entailed(p))
    return true;

  pval_t old_val = s.state.p_vals[p.pid];
  if(!s.state.post(p)) {
    // Setup conflict
    set_confl(s, p, r, s.infer.confl); 
    return false;
  }
  // s.pred_origin[p.pid] = active_prop;

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
  if(elt.watch)
    return elt.watch->ws;

  patom_t p(~elt.atom);
  watch_node* watch = s.infer.get_watch(p.pid, p.val);
  elt.watch = watch;
  return watch->ws;
}

//inline
bool update_watchlist(solver_data& s,
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
    // No watches found; either unit or conflicting.
    c[1] = elt;
    ws[jj++] = ch;
    // Save the trail location, so we can tell if it's locked.
    c.extra.depth = s.infer.trail.size();
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

forceinline
bool propagate_ineqs(solver_data& s, pid_t p) {
  pval_t val_p = s.state.p_vals[p];

  for(infer_info::bin_le ineq : s.infer.pred_ineqs[p]) {
    pval_t val_q = val_p + ineq.offset;
    if(s.state.p_vals[ineq.p] >= val_q)
      continue;
    if(!enqueue(s, patom_t { ineq.p, val_q }, reason(p, ineq.offset)))
      return false;
  }
  return true;
}

forceinline
bool propagate_pred(solver_data& s, pid_t p) {
  // Process watches
  watch_node* curr = s.infer.pred_watches[p];
  patom_t atom(p, curr->succ_val);
  while(s.state.is_entailed(atom)) {
    curr = curr->succ;

    if(!update_watchlist(s, ~atom, curr->ws)) {
      return false;
    }
    for(watch_callback call : curr->callbacks)
      call();
    atom.val = curr->succ_val;
  }

  // Propagate binary inequalities
  if(!propagate_ineqs(s, p))
    return false;

  // Trail head of watches 
  if(curr != s.infer.pred_watches[p]) {
    // FIXME: This may not be safe.
    // If new preds are introduced during search, the
    // pred_watches vector may be resized, invalidating
    // the previous trail entries.
    trail_change(s.persist, s.infer.pred_watches[p], curr);
  }
   
  return true;
}

// Record that the value of p has changed at the
// current decision level.
forceinline void touch_pred(solver_data& s, pid_t p) {
  if(!s.persist.pred_touched[p]) {
    s.persist.pred_touched[p] = true;
    s.persist.touched_preds.push(p);
  }
}

forceinline void wakeup_pred(solver_data& s, pid_t p) {
  // assert(!is_bool(s, p)); // Handle Bool wake-up separately
  for(watch_callback call : s.pred_callbacks[p])
    call();
  s.wake_queued[p] = false;
}

// FIXME: Allow attachment to patoms.
void attach(solver_data* s, patom_t p, const watch_callback& cb) {
  watch_node* watch = s->infer.get_watch(p.pid, p.val);
  watch->callbacks.push(cb);
}

void prop_cleanup(solver_data& s) {
  // Make sure all modified preds are touched
  while(!s.pred_queue.empty()) {
    pid_t pi = s.pred_queue._pop();
    s.pred_queued[pi] = false;
    touch_pred(s, pi);
  }
  for(pid_t pi : s.wake_queue) {
    touch_pred(s, pi);
  }
  s.wake_queue.clear();

  while(!s.prop_queue.empty()) {
    propagator* p = s.prop_queue._pop();
    p->cleanup();
  }
  // s.active_prop = nullptr;
}

bool propagate(solver_data& s) {
  // Initialize any lazy predicates
  if(s.state.init_end != s.state.initializers.size()) {
    vec<pinit_data>& inits(s.state.initializers);
    unsigned int& end = s.state.init_end;

    // FIXME: Trailing should probably be done in push_level.
    trail_push(s.persist, end);
    for(int ii = end; ii != inits.size(); ++ii) {
      pid_t p(inits[ii].pi<<1); 
      initialize(p, inits[end].init, s.state.p_last);
      initialize(p, inits[end].init, s.state.p_vals);
      // If this is at its initial value, discard it.
      if(s.state.p_vals[p] != s.state.p_root[p]
        || s.state.p_vals[p+1] != s.state.p_root[p+1])
        inits[end++] = inits[ii];
    }
    inits.shrink(inits.size() - end);
  }

  // Propagate any entailed clauses
  while(!s.pred_queue.empty()) {
prop_restart:
    pid_t pi = s.pred_queue._pop();
    // We rely on wake_queue to
    s.pred_queued[pi] = false;
    if(!s.wake_queued[pi]) {
      s.wake_queue.push(pi);
      s.wake_queued[pi] = true;
    }

    if(!propagate_pred(s, pi)) {
      prop_cleanup(s);
      return false;
    }
  }
  
  // Fire any events for the changed predicates
  for(pid_t pi : s.wake_queue) {
    assert(0 <= pi && pi < num_preds(&s));
    touch_pred(s, pi);
    wakeup_pred(s, pi);  
  }
  s.wake_queue.clear();

  // Process enqueued propagators
  while(!s.prop_queue.empty()) {
    propagator* p = s.prop_queue._pop();
    // s.active_prop = p;
    if(!p->propagate(s.infer.confl)) {
      p->cleanup();
      prop_cleanup(s);
      return false; 
    }
    p->cleanup();

    // If one or more predicates were updated,
    // jump back to 
    if(!s.pred_queue.empty()) {
      // s.active_prop = nullptr;
      goto prop_restart;
    }
  }
  return true;
}

//inline
void add_learnt(solver_data* s, vec<clause_elt>& learnt) {
  // Allocate the clause
  // WARN("Collection of learnt clauses not yet implemented.");

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
    s->infer.learnts.push(c);
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
    pval_t head_val = s.infer.pred_watch_heads[pi].val;
    watch_node* head = s.infer.pred_watch_heads[pi].ptr;
    watch_node* dest = s.infer.pred_watches[pi];

    while(head != dest) {
      s.infer.watch_maps[pi].rem(head_val);
      watch_node* w = head;
      head_val = head->succ_val;
      head = head->succ; 
      delete w;
    }
    s.infer.pred_watch_heads[pi].val = head_val;
    s.infer.pred_watch_heads[pi].ptr = head;
    /*
    while(s.infer.pred_watch_heads[pi] != s.infer.pred_watches[pi]) {
      watch_node* w = s.infer.pred_watch_heads[pi];
      s.infer.pred_watch_heads[pi] = w->succ;
      s.infer.watch_maps[pi].rem(watch_val);
      delete w;
    }
    */
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

// Retrieve a model
// precondition: last call to solver::solve returned SAT
// actually, we should just save the last incumbent.
void save_model(solver_data* data) {
  data->incumbent.vals.clear(); 
  vec<pval_t>& vals(data->state.p_vals);
  for(pid_t pi : num_range(0, vals.size()/2))
    data->incumbent.vals.push(vals[2*pi]);
}
  
model solver::get_model(void) {
  return data->incumbent;
}

// Solving
solver::result solver::solve(void) {
  // Top-level failure
  sdata& s(*data);
  int confl_num = 0;

  int restart_lim = s.opts.restart_limit;
  // FIXME: On successive runs, this may be smaller than
  // the existing database
  int gc_lim = s.opts.learnt_dbmax; 

  int next_restart = restart_lim;
  int next_gc = gc_lim - s.infer.learnts.size();
  int next_pause = std::min(next_restart, next_gc);

  while(true) {
    if(!propagate(s)) {
      ++confl_num;
#ifdef LOG_ALL
      std::cout << "Conflict: " << s.infer.confl << std::endl;
#endif
      if(decision_level(s) == 0) {
        s.stats.conflicts += confl_num;
        return UNSAT;
      }
        
      // Conflict
      int bt_level = compute_learnt(&s, s.infer.confl);
#ifdef LOG_ALL
      std::cout << "Learnt: " << s.infer.confl << std::endl;
#endif
      bt_to_level(&s, bt_level);

#ifdef CHECK_STATE
      check_pvals(&s);
#endif

      add_learnt(&s, s.infer.confl);
      s.infer.confl.clear();

      if(confl_num == next_pause) {
        s.stats.conflicts += confl_num;
        next_restart -= confl_num;
        next_gc -= confl_num;

        confl_num = 0;

        if(next_restart == 0) {
#ifdef LOG_ALL
          std::cout << "[| Restarting |]" << std::endl;
#endif
          s.stats.restarts++;
  
          next_restart = restart_lim = restart_lim * s.opts.restart_growthrate;
          if(decision_level(s) > 0)
            bt_to_level(&s, 0);
        }
        if(next_gc == 0) {
#ifdef LOG_ALL
          std::cout << "[| GC |]" << std::endl;
#endif
          reduce_db(&s);

          gc_lim = gc_lim * s.opts.learnt_growthrate;
          next_gc = gc_lim - s.infer.learnts.size();
        }

        next_pause = std::min(next_restart, next_gc);
      }
      continue;
    }

    if(decision_level(s) == 0)
      simplify_at_root(s);

    patom_t dec = branch(&s);
    if(dec == at_Undef) {
      save_model(data);
      s.stats.conflicts += confl_num;
      s.stats.solutions++;
      return SAT;
    }

    assert(!s.state.is_entailed(dec));
    assert(!s.state.is_inconsistent(dec));
#ifdef LOG_ALL
    std::cout << "?" << s.infer.trail_lim.size() << "> " << dec << std::endl;
#endif

    push_level(&s);
    enqueue(s, dec, reason());
  }

  // Unreachable
  return SAT;
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
