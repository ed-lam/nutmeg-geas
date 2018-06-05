#include <climits>
#include <unordered_map>

#include "mtl/Heap.h"
#include "solver/solver_data.h"
#include "solver/solver_ext.h"
#include "engine/propagator.h"
#include "engine/propagator_ext.h"
// #include "constraints/difflogic.h"
#include "vars/intvar.h"
#include "mtl/bool-set.h"
#include "mtl/min-tree.h"

using namespace geas;

class diff_manager : public propagator, public prop_inst<diff_manager>, public solver_ext<diff_manager> {
public:
  typedef unsigned int diff_id;
  typedef unsigned int dim_id;
  typedef unsigned int cst_id;

  diff_manager(solver_data* s)
    : propagator(s), finished(0), finished_sz(0),
      fqueue(cmp_fwd_dist { this }),
      rqueue(cmp_rev_dist { this }) {
     
  }

  struct diff_info {
    // Everything else should be default initialized.
    diff_info(dim_id _x, dim_id _y, int _wt)
      : x(_x), y(_y), wt(_wt), is_active(false)
    { }

    dim_id x;
    dim_id y;
    int wt;

    int wit; // If still suspended, a witness for satisfiability.
    patom_t r; // If active, the activator
    int sep; // If killed because of bounds, ub(y) + v < sep <= lb(x)
    bool is_active;

    // The position of c in the lb/ub lists.
    unsigned int x_idx;
    unsigned int y_idx;

    // r_1 \/ r_2 \/ ... \/ r_n -> x <= y+k
    vec<patom_t> rs; // Possible activators
  };

  struct act_info {
    dim_id y;
    int wt;
    cst_id c;
  };

  struct activator {
    patom_t r;
    cst_id c; 
  };

  struct eval_lb_wit {
    int operator()(cst_id c) const {
      if(d->finished.elem(c))
        return INT_MAX;
      return d->csts[c].wit;
    }
    diff_manager* d;
  };
  struct eval_ub_wit {
    int operator()(cst_id c) const {
      if(d->finished.elem(c))
        return INT_MAX;
      return -d->csts[c].wit - d->csts[c].wt;
    }
    diff_manager* d;
  };

  struct dim_info {
    dim_info(diff_manager* d)
      : lb_act(), ub_act(), csts_lb(), csts_ub(),
        threshold_lb(eval_lb_wit {d}), threshold_ub(eval_ub_wit {d}),
        l_rel(false), r_rel(false) { }

    vec<act_info> lb_act;
    vec<act_info> ub_act;

    vec<cst_id> csts_lb;
    vec<cst_id> csts_ub;

    bound_tree<int, eval_lb_wit> threshold_lb;
    bound_tree<int, eval_ub_wit> threshold_ub;

    bool l_rel;
    bool r_rel;
  };

  void check_potential(void) {
    for(dim_id d : irange(dims.size())) {
      for(act_info act : dims[d].lb_act) {
        assert(pot[d] + act.wt - pot[act.y] >= 0);
      }
    }
  }

  struct cmp_fwd_dist {
    bool operator()(dim_id x, dim_id y) const {
      if(d->fdist[x] - d->pot[x] == d->fdist[y] - d->pot[y])
        return d->flag[x] < d->flag[y];
      return d->fdist[x] - d->pot[x] < d->fdist[y] - d->pot[y];
    }
    diff_manager* d;
  };
  struct cmp_rev_dist {
    bool operator()(dim_id x, dim_id y) const {
      if(d->rdist[x] + d->pot[x] == d->rdist[y] + d->pot[y])
        return d->flag[x] < d->flag[y];
      return d->rdist[x] + d->pot[x] < d->rdist[y] + d->pot[y];
    }
    diff_manager* d;
  };

  // Can't use finished.elem directly, because
  // we haven't yet untrailed.
  inline bool is_finished(cst_id c) {
    return finished.pos(c) < finished_sz;
  }

  watch_result wake_r(int ri) {
    if(!is_finished(activators[ri].c)) {
      act_queue.push(ri);
      queue_prop();  
    }
    return Wt_Keep;
  }
  watch_result wake_lb(int di) {
    if(!lb_change.elem(di)) {
      lb_change.add(di);
      queue_prop();
    }
    return Wt_Keep;
  }
  watch_result wake_ub(int di) {
    if(!ub_change.elem(di)) {
      ub_change.add(di);
      queue_prop();
    }
    return Wt_Keep;
  }

  void cleanup(void) {
    is_queued = false;
    act_queue.clear();
    lb_change.clear();
    ub_change.clear();
    lb_check.clear();
    ub_check.clear();
  }
  
  bool propagate(vec<clause_elt>& confl) {
    // If we've backtracked since the last execution,
    // restore the state.
    // Don't need to untrail on failure, because any
    // changes will get reverted on the next run.
    untrail(); 

    // Process newly activated constraints.
    for(unsigned int ai : act_queue) {
      activator a(activators[ai]);
      if(!activate(a.c, a.r, confl))
        return false;
    }
    // Now bounds. Process active constraints
    // before processing suspended.
    for(dim_id v : lb_change) {
      if(lb_check.elem(v))
        continue;
      if(!propagate_active_lb(v))
        return false;
    }
    for(dim_id v : ub_change) {
      if(ub_check.elem(v))
        continue;
      if(!propagate_active_ub(v))
        return false;
    }
    // And now repair witnesses.
    // FIXME: we should also run propagate_suspended_Xb
    // for anything updated by propagate_active_Xb.
    for(dim_id v : lb_check) {
      if(!propagate_suspended_lb(v))
        return false;
    }
    for(dim_id v : ub_check) {
      if(!propagate_suspended_ub(v))
        return false;
    }
    // If we made it this far, commit to the changes.
    set(finished_sz, finished.size());
    return true;
  }

  // Post a new constraint r -> (x - y <= k)
  bool post(patom_t r, intvar x, intvar y, int k);

  // Propagate
  bool activate(cst_id c, patom_t r, vec<clause_elt>& confl);
  bool propagate_active_lb(dim_id d);
  bool propagate_active_ub(dim_id d);
  bool propagate_suspended_lb(dim_id d);
  bool propagate_suspended_ub(dim_id d);
  bool process_killed(cst_id c);
  
  void untrail(void);
   
  bool repair_potential(dim_id s, dim_id d, int wt);
  bool exists_path(dim_id s0, dim_id d0, int cap, unsigned int timestamp);

  void queue_fwd(dim_id d, int wt, diff_id r);
  void queue_rev(dim_id d, int wt, diff_id r);

  void ex_lb(int c, pval_t p, vec<clause_elt>& expl);
  void ex_ub(int c, pval_t p, vec<clause_elt>& expl);
  void ex_r_bnd(int c, pval_t p, vec<clause_elt>& expl);
  void ex_r_diff(int c, pval_t p, vec<clause_elt>& expl);

  dim_id get_dim(intvar x);

  vec<intvar> vars;
  vec<dim_info> dims;

  vec<diff_info> csts; 
  p_sparseset finished;
  Tuint finished_sz;

  vec<activator> activators;

  // Potential function: for all active (x -(wt)-> y),
  // pot(y) + wt - pot(x) >= 0.
  vec<int> pot;

  // Transient stuff. Should really factor these out.
  vec<bool> flag;
  vec<int> fdist;
  vec<int> fpred;
  boolset fseen;
  Heap<cmp_fwd_dist> fqueue;

  vec<int> rdist;
  vec<int> rpred;
  boolset rseen;
  Heap<cmp_rev_dist> rqueue;

  // Changes to deal with when the propagator runs.
  vec<unsigned int> act_queue; // Which activations have occurred 
  boolset lb_change; boolset lb_check;
  boolset ub_change; boolset ub_check;

  // Mapping variables to dimensions
  std::unordered_map<geas::pid_t, dim_id> dim_map;
};

// Need to compute new potential pot' s.t. pot'[d] + wt - pot[s] >= 0.
bool diff_manager::repair_potential(dim_id s, dim_id d, int wt) {
  // Compute the change in potential.
  // To avoid creating a new comparator, we offset all
  // weights by pot[d].
  assert(fseen.size() == 0);
  assert(fqueue.empty());
  fdist[d] = pot[s] + wt /* - pot[d] */;
  assert(fdist[d] < 0);
  fseen.add(d);
  fqueue.insert(d);

  while(!fqueue.empty()) {
    int r = fqueue.removeMin();
    int p = /* pot[r] + */ fdist[r];
    for(act_info act : dims[r].lb_act) {
      if(!fseen.elem(act.y)) {
        if(p + act.wt - pot[act.y] >= 0)
          continue;
        if(act.y == s) {
          // Found a negative weight loop from d to s.
          fpred[s] = act.c;
          fseen.clear();
          fqueue.clear();
          return false;
        }
        fdist[act.y] = p + act.wt /* - pot[act.y] */;
        fpred[act.y] = act.c;
        fseen.add(act.y);
        fqueue.insert(act.y);
      } else {
        if(p + act.wt /* - pot[act.y] */ < fdist[act.y]) {
          assert(fqueue.inHeap(act.y));
          fdist[act.y] = p + act.wt /* - pot[act.y] */;
          fpred[act.y] = act.c;
          fqueue.decrease(act.y);
        }
      }
    }
  }

  // Successfully computed; update pot.
  for(dim_id p : fseen)
    pot[p] = /* pot[p] + */ fdist[p];

  assert(pot[s] + wt - pot[d] >= 0);
  check_potential();

  fseen.clear();
  return true;
}

// Bidirectional search, through only active edges.
void diff_manager::queue_fwd(dim_id d, int wt, diff_id r) {
  if(fseen.elem(d)) {
    if(wt < fdist[d]) {
      assert(fqueue.inHeap(d));
      fdist[d] = wt;
      fpred[d] = r;
      fqueue.decrease(d);
    }
  } else {
    fdist[d] = wt;
    fpred[d] = r;
    fseen.add(d);
    fqueue.insert(d);
  }
}
// Bidirectional search, through only active edges.
void diff_manager::queue_rev(dim_id d, int wt, diff_id r) {
  if(rseen.elem(d)) {
    if(wt < rdist[d]) {
      assert(rqueue.inHeap(d));
      rdist[d] = wt;
      rpred[d] = r;
      rqueue.decrease(d);
    }
  } else {
    rdist[d] = wt;
    rpred[d] = r;
    rseen.add(d);
    rqueue.insert(d);
  }
}

bool diff_manager::exists_path(dim_id s0, dim_id d0, int cap, unsigned int timestamp) {
  queue_fwd(s0, 0, INT_MAX);
  queue_rev(d0, 0, INT_MAX);
  int fmin(0);
  int rmin(0);
  // int best(INT_MAX);

  bool ret = false;
  while(fmin + rmin < cap) {
    if(fmin <= rmin) {
      dim_id s(fqueue.removeMin());
      for(act_info e : dims[s].lb_act) {
        // The remaining edges weren't at the time of inference.
        if(finished.pos(e.c) >= timestamp)
          break;
        if(rseen.elem(e.y)) {
          int wt(fmin + e.wt + rdist[e.y]);
          if(wt <= cap) {
            // Found a path. Set the rest of fpred.
            dim_id d(e.y);
            fpred[d] = e.c;
            while(d != d0) {
              cst_id c(rpred[d]);   
              fpred[csts[c].y] = c;
              d = csts[c].y;
            }
            ret = true;
            break;
          }
        } else {
          queue_fwd(e.y, fmin + e.wt, e.c);
        }
      }
      fmin = fqueue.getMin();
    } else {
      dim_id d(rqueue.removeMin());
      for(act_info e : dims[d].ub_act) {
        if(finished.pos(e.c) >= timestamp)
          break;
        if(fseen.elem(e.y)) {
          spval_t wt(fmin + e.wt + fdist[e.y]);
          if(wt <= cap) {
            // Found a solution
            fpred[d] = e.c;
            while(d != d0) {
              cst_id c(rpred[d]);   
              fpred[csts[c].y] = c;
              d = csts[c].y;
            }
            ret = true;
            break;
          }
        } else {
          queue_rev(e.y, rmin + e.wt, e.c);
        }
      }
    }
  }
  fqueue.clear(); fseen.clear();
  rqueue.clear(); rseen.clear();
  // At this point, we've proven the shortest
  // path is has length greater than cap.
  return ret;
}


void diff_manager::ex_lb(int c, pval_t p, vec<clause_elt>& expl) {
  // lb(y) >= lb(x) - c.wt  
  const diff_info& ci(csts[c]);
  int v(vars[ci.y].lb_of_pval(p));
  EX_PUSH(expl, ~ci.r);
  EX_PUSH(expl, vars[ci.x] < v + ci.wt);
}
void diff_manager::ex_ub(int c, pval_t p, vec<clause_elt>& expl) {
  const diff_info& ci(csts[c]);
  int v(vars[ci.x].ub_of_pval(p));
  EX_PUSH(expl, ~ci.r);
  EX_PUSH(expl, vars[ci.y] > v - ci.wt);
}

// (x <= y+k) false, because lb(x) > ub(y)+k.
void diff_manager::ex_r_bnd(int c, pval_t _p, vec<clause_elt>& expl) {
  const diff_info& ci(csts[c]);
  EX_PUSH(expl, vars[ci.x] < ci.sep); 
  EX_PUSH(expl, vars[ci.y] >= ci.sep - ci.wt);
}

// (x <= y+k) false, because of some chain of active constraints
void diff_manager::ex_r_diff(int c, pval_t _p, vec<clause_elt>& expl) {
  const diff_info& ci(csts[c]);
  // Find some path such that adding c would introduce a negative cycle
  if(!exists_path(ci.y, ci.x, - ci.wt - 1, finished.pos(c)))
    ERROR;
  // Now collect the explanation
  dim_id p(ci.x);
  while(p != ci.y) {
    cst_id c_r = fpred[p];
    EX_PUSH(expl, ~csts[c_r].r);
    p = csts[c_r].x;
  }
}

auto diff_manager::get_dim(intvar x) -> dim_id {
  auto it(dim_map.find(x.p));
  if(it != dim_map.end())
    return (*it).second;

  // Otherwise, we need to allocate all the helper data.
  dim_id d(vars.size());
  vars.push(x);
  dims.push(dim_info(this));
  pot.push(0);

  flag.push(0);
  fdist.push(0); fpred.push(INT_MAX); fseen.growTo(d+1);
  rdist.push(0); rpred.push(INT_MAX); rseen.growTo(d+1);

  lb_change.growTo(d+1); ub_change.growTo(d+1);
  lb_check.growTo(d+1); ub_check.growTo(d+1);

  dim_map.insert(std::make_pair(x.p, d)); 

  x.attach(E_LB, watch<&P::wake_lb>(d));
  x.attach(E_UB, watch<&P::wake_ub>(d));
  return d;
}

bool diff_manager::post(patom_t r, intvar x, intvar y, int k) {
  // If the constraint is already deactivated,
  // forget it.
  if(!r.ub(s->ctx()))
    return true;

  // First, find the dimensions corresponding to some offset of x.
  dim_id dx(get_dim(x));
  dim_id dy(get_dim(y));
  assert(vars[dx].p == x.p);
  assert(vars[dy].p == y.p);
  // Reformulate the constraint in terms of our dimensions.
  k += (vars[dx].off - x.off);
  k -= (vars[dy].off - y.off);

  cst_id ci = csts.size();
  finished.growTo_strict(ci+1);

  csts.push(diff_info(dx, dy, k));
  diff_info& di(csts.last());
  di.rs.push(r);

  if(r.lb(s->ctx())) {
    // Already active
    check_potential();

    if(pot[dx] + k - pot[dy] < 0 && !repair_potential(dx, dy, k))
      return false;
    
    di.r = r;
    di.is_active = true;
    dims[dx].lb_act.push(act_info { dy, k, ci });
    dims[dy].ub_act.push(act_info { dx, k, ci });
    lb_change.add(dx);
    ub_change.add(dy);
    check_potential();
    // Worry about the rest later.
  } else {
    // Suspended
    if(lb(vars[dx]) - ub(vars[dy]) > k) {
      // Should already be false
      if(!enqueue(*s, ~r, reason()))
        return false;
    }
    // if not, set the witness and set up the watches.
    attach(s, r, watch<&P::wake_r>(activators.size()));
    activators.push(activator { r, ci });

    int m = lb(vars[dx]) + (ub(vars[dy]) - lb(vars[dx]) + k)/2;
    di.wit = m; 
    di.x_idx = dims[dx].csts_lb.size();
    di.y_idx = dims[dy].csts_ub.size();
    dims[dx].csts_lb.push(ci);
    dims[dy].csts_ub.push(ci);
    dims[dx].threshold_lb.push(ci);
    dims[dy].threshold_ub.push(ci);
  }
  return true;
}

bool diff_manager::activate(cst_id c, patom_t act, vec<clause_elt>& confl) {
  // First, check if the constraint is already active.
  // If the constraint was removed due to failing, act should have been
  // set false, so we _should_ have already detected a conflict.
  if(finished.elem(c))
    return true;
  
  // After this, the constraint is either
  // active or entailed
  finished.insert(c);

  // Check if the potential function needs repair.
  diff_info& ci(csts[c]);
  if(pot[ci.x] + ci.wt - pot[ci.y] >= 0) {
    // Potential function is already valid. Check
    // if the constraint is already entailed.
    if(exists_path(ci.x, ci.y, ci.wt, finished.size()))
      return true;
  } else {
    // Check if the potential function can be repaired.
    // If this fails, it should have set the constraint chain
    // in fpred.
    if(!repair_potential(ci.x, ci.y, ci.wt)) {
      // Collect the corresponding failure, and abort.
      EX_PUSH(confl, ~act);  
      dim_id d_r(ci.x);
      do {
        cst_id c_r(fpred[d_r]);
        EX_PUSH(confl, ~csts[c_r].r);
        d_r = csts[c_r].x;
      } while (d_r != ci.y);
      return false;
    }
  }
  // The potential function is now consistent, so
  // set up the bookkeeping for c.
  ci.r = act;
  ci.is_active = true;
  dims[ci.x].lb_act.push(act_info { ci.y, ci.wt, c });
  dims[ci.y].ub_act.push(act_info { ci.x, ci.wt, c });
  check_potential();
  // Find all constraints which are made inconsistent
  if(!process_killed(c))
    return false;
  // Now update lower and upper bounds.
  if(lb(vars[ci.x]) + ci.wt > lb(vars[ci.y])) {
    if(!set_lb(vars[ci.y], lb(vars[ci.x]) - ci.wt, expl<&P::ex_lb>(c)))
      return false;
    if(!propagate_active_lb(ci.y))
      return false;
  }
  if(ub(vars[ci.x]) > ub(vars[ci.y]) - ci.wt) {
    if(!set_ub(vars[ci.x], ub(vars[ci.y]) + ci.wt, expl<&P::ex_ub>(c)))
      return false;
    if(!propagate_active_ub(ci.x))
      return false;
  }
  return true;
}

// Identify any suspended constraints which are inconsistent
// after adding c.
bool diff_manager::process_killed(cst_id c) {
  // Run forward and backward passes to compute
  // relevant nodes. First bit in distance indicates whether it
  // passed through the new edge.
  const diff_info& ci(csts[c]);
  {
    int flag_count = 1;
    fdist[ci.x] = 0; flag[ci.x] = 0; fseen.add(ci.x); fqueue.insert(ci.x);
    fdist[ci.y] = ci.wt; flag[ci.y] = 1; fseen.add(ci.y); fqueue.insert(ci.y);
    while(!fqueue.empty()) {
      dim_id s(fqueue.removeMin());
      int s_wt = fdist[s];
      if(flag[s])
        dims[s].l_rel = true;
      for(act_info act : dims[s].lb_act) {
        if(!fseen.elem(act.y)) {
          fdist[act.y] = s_wt + act.wt; flag[act.y] = flag[s];
          fseen.add(act.y); fqueue.insert(act.y);
          flag_count += flag[s];
        } else {
          if(s_wt + act.wt < fdist[act.y]) {
            assert(fqueue.inHeap(act.y));
            flag_count += flag[s] - flag[act.y];
            fdist[act.y] = s_wt + act.wt; flag[act.y] = flag[s];
            fqueue.decrease(act.y);
          } else if(s_wt + act.wt == fdist[act.y] && flag[s] < flag[act.y]) {
            flag_count += flag[s] - flag[act.y];
            flag[act.y] = flag[s];
            fqueue.decrease(act.y);
          }
        }
      }
      flag_count -= flag[s];
      flag[s] = 0;
      if(!flag_count) {
        fqueue.clear();
        break;
      }
    }
  }
  {
    int flag_count = 1;
    rdist[ci.y] = 0; flag[ci.y] = 0; rseen.add(ci.y); rqueue.insert(ci.y);
    rdist[ci.x] = ci.wt; flag[ci.x] = 1; rseen.add(ci.x); rqueue.insert(ci.x);
    while(!rqueue.empty()) {
      dim_id d(rqueue.removeMin());
      int d_wt = rdist[d];
      if(flag[d])
        dims[d].r_rel = true;
      for(act_info act : dims[d].ub_act) {
        if(!rseen.elem(act.y)) {
          flag_count += flag[d];
          rdist[act.y] = d_wt + act.wt; flag[act.y] = flag[d];
          rseen.add(act.y); rqueue.insert(act.y); 
        } else {
          if(d_wt + act.wt < rdist[act.y]) {
            assert(rqueue.inHeap(act.y));
            flag_count += flag[d] - flag[act.y];
            rdist[act.y] = d_wt + act.wt; flag[act.y] = flag[d];
            rqueue.decrease(act.y);
          } else if(d_wt + act.wt == rdist[act.y] && flag[d] < flag[act.y]) {
            assert(rqueue.inHeap(act.y));
            flag_count += flag[d] - flag[act.y];
            flag[act.y] = flag[d];
            rqueue.decrease(act.y);
          }
        }
        flag_count -= flag[d];
        flag[d] = 0;
        if(!flag_count) {
          rqueue.clear();
          break;
        }
      }
    }
  }
  
  // Now we walk through _all_ suspended constraints,
  // checking for entailment.
  // TODO: Make more incremental
  bool ret = true;
  int relev = 0;
  for(int e : finished.complement()) {
    assert(e < csts.size());
    const diff_info& ei(csts[e]);
    assert(ei.x < (unsigned int) dims.size());
    assert(ei.y < (unsigned int) dims.size());
    if(dims[ei.x].l_rel && dims[ei.y].r_rel) {
      ++relev;
      if((rdist[ei.x]>>1) - ci.wt + (fdist[ei.y]>>1) < - ei.wt) {
        // Inconsistent
        finished.insert(e);
        for(patom_t r : ei.rs) {
          if(!enqueue(*s, ~r, expl<&P::ex_r_diff>(e))) {
            ret = false;
            goto killed_cleanup;
          }
        }
      }
    }
  }
killed_cleanup:
  // Cleanup 
  for(dim_id d : fseen)
    dims[d].l_rel = false;
  for(dim_id s : rseen)
    dims[s].r_rel = false;
  fseen.clear(); rseen.clear();

  return ret;
}

// TODO: If a bound had changed, but it was updated during
// propagate_active_lb, we don't need to touch it again.
bool diff_manager::propagate_active_lb(dim_id d) {
  int v(lb(vars[d]));
  lb_check.add(d);
  for(act_info act : dims[d].lb_act) {
    // Skip variables with unchanged bounds
    if(!fseen.elem(act.y)) {
      if(v - act.wt <= lb(vars[act.y]))
        continue;
      fdist[act.y] = act.wt;
      fpred[act.y] = act.c;
      fseen.add(act.y);
      fqueue.insert(act.y);
    } else {
      if(act.wt < fdist[act.y]) {
        assert(fqueue.inHeap(act.y));
        fdist[act.y] = act.wt;
        fpred[act.y] = act.c;
        fqueue.decrease(act.y);
      }
    }
  }
  while(!fqueue.empty()) {
    dim_id s(fqueue.removeMin());
    int s_wt = fdist[s];
    if(!set_lb(vars[s], v - fdist[s], expl<&P::ex_lb>(fpred[s]))) {
      fseen.clear(); fqueue.clear();
      return false; 
    }
    lb_check.add(s);
    // Now process any children
    for(act_info act : dims[s].lb_act) {
      if(!fseen.elem(act.y)) {
        if(v - s_wt - act.wt <= lb(vars[act.y]))
          continue;
        fdist[act.y] = s_wt + act.wt;
        fpred[act.y] = act.c;
        fseen.add(act.y);
        fqueue.insert(act.y);
      } else {
        if(s_wt + act.wt < fdist[act.y]) {
          assert(fqueue.inHeap(act.y));
          fdist[act.y] = s_wt + act.wt;
          fpred[act.y] = act.c;
          fqueue.decrease(act.y);
        }
      }
    }
  }
  fseen.clear();
  return true;
}

bool diff_manager::propagate_active_ub(dim_id d) {
  int v(ub(vars[d]));
  ub_check.add(d);
  for(act_info act : dims[d].ub_act) {
    // Skip variables with unchanged bounds
    if(!rseen.elem(act.y)) {
      if(v + act.wt >= ub(vars[act.y]))
        continue;
      rdist[act.y] = act.wt;
      rpred[act.y] = act.c;
      rseen.add(act.y);
      rqueue.insert(act.y);
    } else {
      if(act.wt < rdist[act.y]) {
        assert(rqueue.inHeap(act.y));
        rdist[act.y] = act.wt;
        rpred[act.y] = act.c;
        rqueue.decrease(act.y);
      }
    }
  }
  while(!rqueue.empty()) {
    dim_id s(rqueue.removeMin());
    int s_wt = rdist[s];
    if(!set_ub(vars[s], v + rdist[s], expl<&P::ex_ub>(rpred[s]))) {
      rseen.clear(); rqueue.clear();
      return false; 
    }
    ub_check.add(s);
    // Now process any children
    for(act_info act : dims[s].ub_act) {
      if(!rseen.elem(act.y)) {
        if(v + s_wt + act.wt >= ub(vars[act.y]))
          continue;
        rdist[act.y] = s_wt + act.wt;
        rpred[act.y] = act.c;
        rseen.add(act.y);
        rqueue.insert(act.y);
      } else {
        if(s_wt + act.wt < rdist[act.y]) {
          assert(rqueue.inHeap(act.y));
          rdist[act.y] = s_wt + act.wt;
          rpred[act.y] = act.c;
          rqueue.decrease(act.y);
        }
      }
    }
  }
  rseen.clear();
  return true;
}

void diff_manager::untrail(void) {
  if(finished.size() == finished_sz)
    return;
  int ii = finished.size();
  // Need to reset finished.sz so that we get the correct
  // witnesses.
  finished.sz = finished_sz;
  for(--ii; ii >= (int) finished_sz; --ii) {
    // Urgh. We need an extra parameter, so we can tell
    // whether the constraint needs to be removed from
    // the active lists.
    cst_id c(finished[ii]); 
    if(csts[c].is_active) {
      // Remove it from the corresponding active lists.
      dims[csts[c].x].lb_act.pop();
      dims[csts[c].y].ub_act.pop();
      csts[c].is_active = false;
    }
    // In either case, repair the witnesses.
    dims[csts[c].x].threshold_lb.decrease(csts[c].x_idx); 
    dims[csts[c].y].threshold_ub.decrease(csts[c].y_idx); 
  }
}

bool diff_manager::propagate_suspended_lb(dim_id d) {
  int v(lb(vars[d]));
  dim_info& di(dims[d]);
  
  // Process all the suspended constraints, with separator
  // strictly less than v.
  return di.threshold_lb.forall_lt([&](int ci) {
    // Check if there is a replacement separator.
    diff_info& c(csts[ci]);
    int w(ub(vars[c.y]));
    if(v > w + c.wt) {
      // Constraint is now dead. Kill all the
      // activators, and de-suspend the constraint.
      c.sep = v;   
      for(patom_t r : c.rs) {
        if(!enqueue(*s, ~r, expl<&P::ex_r_bnd>(ci)))
          return false;
      }
      finished.insert(ci);
    } else {
      // Choose a new separator.
      int s = v + (v - c.wt - w)/2;
      c.wit = s;
      dims[c.y].threshold_ub.decrease(c.y_idx);
    }
    return true;
  }, v);
}

bool diff_manager::propagate_suspended_ub(dim_id d) {
  int v(ub(vars[d]));
  dim_info& di(dims[d]);
  
  // Process all the suspended constraints, with separator
  // strictly less than v.
  return di.threshold_ub.forall_lt([&](int ci) {
    // Check if there is a replacement witness.
    diff_info& c(csts[ci]);
    int w(lb(vars[c.x]));
    if(w > v + c.wt) {
      // Constraint is now dead. Kill all the
      // activators, and de-suspend the constraint.
      c.sep = v + c.wt + 1;
      for(patom_t r : c.rs) {
        if(!enqueue(*s, ~r, expl<&P::ex_r_bnd>(ci)))
          return false;
      }
      finished.insert(ci);
    } else {
      // Choose a new witness.
      int s = w + (w - c.wt - v)/2;
      c.wit = s;
      dims[c.x].threshold_lb.decrease(c.x_idx);
    }
    return true;
  }, -v);
}

namespace geas {
namespace difflogic {

bool post(solver_data* s, patom_t r, intvar x, intvar y, int k) {
  diff_manager* man(diff_manager::get(s));  
  return man->post(r, x, y, k);
}

bool check_sat(solver_data* s, patom_t r, intvar x, intvar y, int k) {
  NOT_YET;
  return true;
}

}
}
