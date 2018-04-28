#include <cassert>
#include <map>
#include "mtl/Vec.h"
#include "solver/solver_data.h"
#include "vars/intvar.h"

#include "engine/propagator_ext.h"

// #define USE_CHAIN
#define SKIP_L0
// #define EXPL_EAGER
// #define EXPL_NAIVE

namespace geas {

class int_linear_le : public propagator, public prop_inst<int_linear_le> {
  enum { Var_None = -1 };

  /*
  static void wake_x(void* ptr, int xi) {
    int_linear_le* p(static_cast<int_linear_le*>(ptr)); 
    p->queue_prop();     
  }
  static void wake_y(void* ptr, int yi) {
    int_linear_le* p(static_cast<int_linear_le*>(ptr)); 
    p->queue_prop();     
  }
  */
  watch_result wake_x(int xi) { queue_prop(); return Wt_Keep; }
  watch_result wake_y(int xi) { queue_prop(); return Wt_Keep; }
  
  struct elt {
    elt(int _c, intvar _x)
      : c(_c), x(_x) { }
    int c;
    intvar x;
  };

  // Requires backtracking
  void ex_naive(int ei, vec<clause_elt>& expl) {
    for(int xi = 0; xi < xs.size(); xi++) {
      if(xi == ei)
        continue;
      expl.push(xs[xi].x < xs[xi].x.lb(s));
    }
    /*
    for(elt e : p->xs)
      expl.push(e.x < e.x.lb(s));
    for(elt e : p->ys)
      expl.push(e.x > e.x.ub(s));
      */
  }

  static void ex_x(void* ptr, int xi, pval_t pval,
                       vec<clause_elt>& expl) {
    int_linear_le* p(static_cast<int_linear_le*>(ptr));
#ifndef EXPL_NAIVE
    intvar::val_t ival(to_int(pval_inv(pval))+p->xs[xi].x.off);
    intvar::val_t lim(p->k - p->xs[xi].c*(ival+1) + 1);

    intvar::val_t sum = 0;
    for(int xj : irange(xi))
      sum += p->xs[xj].c * p->xs[xj].x.lb(p->s);
    for(int xj : irange(xi+1, p->xs.size()))
      sum += p->xs[xj].c * p->xs[xj].x.lb(p->s);
    p->make_expl(xi, sum - lim, expl);
#else
    // Naive explanation
    for(elt e : p->xs) {
      assert(p->s->state.is_inconsistent(e.x < e.x.lb(p->s)));
      expl.push(e.x < e.x.lb(p->s));
    }
#endif
  }


  public: 

    int_linear_le(solver_data* s, patom_t _r, vec<int>& ks, vec<intvar>& vs, int _k)
      : propagator(s), k(_k)
      {
        if(!s->state.is_entailed_l0(_r))
          assert(0 && "int_linear_le doesn't support reification!");
      for(int ii = 0; ii < vs.size(); ii++) {
        elt e = ks[ii] > 0 ? elt(ks[ii], vs[ii]) : elt(-ks[ii], -vs[ii]);
        e.x.attach(E_LB, watch<&P::wake_x>(xs.size(), Wt_IDEM));
        xs.push(e);
      }
    }

    void root_simplify(void) {
      
    }
    
    template<class E>
    void make_expl(int var, int slack, E& ex) {
      assert(slack >= 0);
#if 0
      for(elt e : xs) {
        assert(s->state.is_inconsistent(e.x < e.x.lb(s)));
        ex.push(e.x < e.x.lb(s));
      }
      for(elt e : ys) {
        assert(s->state.is_inconsistent(e.x > e.x.ub(s)));
        ex.push(e.x > e.x.ub(s));
      }
#else
      vec<int> xs_pending;
      // First, collect things we can omit entirely, or
      // include at the previous decision level
      for(int xi : irange(0, xs.size())) {
        if(xi == var)
          continue;
        elt e = xs[xi];

        int x_lb = e.x.lb(s);
#ifndef SKIP_L0
        int x_lb_0 = lb_0(e.x);
        int diff_0 = e.c * (x_lb - x_lb_0);
        if(diff_0 <= slack) {
          slack -= diff_0;
          continue;
        }
#endif
        int x_lb_p = lb_prev(e.x);
        int diff_p = e.c * (x_lb - x_lb_p);
        if(diff_p <= slack) {
          slack -= diff_p;
          ex.push(e.x < x_lb_p); 
          continue;
        }
        xs_pending.push(xi);
      }

      // Then, add things at the current level
      assert(slack >= 0);
      for(int xi : xs_pending) {
        elt e = xs[xi];
        int diff = slack/e.c;
        ex.push(e.x < e.x.lb(s) - diff);
        slack -= e.c * diff;
        assert(slack >= 0);
      }
#endif
    }

    bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_PROP
      std::cout << "[[Running linear_le]]" << std::endl;
#endif
      int x_lb = 0;
      for(elt e : xs)
        x_lb += e.c * e.x.lb(s);

      if(x_lb > k) {
        // Collect enough atoms to explain the sum.
        // FIXME: This is kinda weak. We really want to
        // push as much as we can onto the previous level.
        make_expl(Var_None, x_lb - k - 1, confl);
        /* /
        for(elt e : xs)
          confl.push(e.x < e.x.lb(s));
        for(elt e : ys)
          confl.push(e.x > e.x.ub(s));
        / */

        // NOT_YET;
#ifdef CHECK_STATE
        assert(confl_is_current(s, confl));
#endif
        return false; 
      }

      // Otherwise, propagate upper bounds.
      int slack = k - x_lb;
      for(int xi : irange(0, xs.size())) {
        elt e = xs[xi];
        int x_diff = slack/e.c;
        int x_ub = e.x.lb(s) + x_diff;
        if(x_ub < e.x.ub(s)) {
          // Build the explanation
          /*
          expl_builder ex(s->persist.alloc_expl(xs.size()+ys.size()));
          make_expl(2*xi, slack - e.c * x_diff, ex);
          if(!e.x.set_ub(x_ub, *ex))
          */
          if(!set_ub(e.x, x_ub,
              expl_thunk { ex_x, this, xi, expl_thunk::Ex_BTPRED }))
//            if(!e.x.set_ub(x_ub,
//                ex_thunk(ex_nil<&P::ex_naive>, 2*xi, expl_thunk::Ex_BTPRED)))
            return false;
        }
      }

      return true;
    }

    vec<elt> xs;
    int k;
};

// Incremental linear le propagator
class lin_le_inc : public propagator, public prop_inst<lin_le_inc> {
  enum { Var_None = -1 };
  enum { S_Active = 1, S_Red = 2 };
  
  struct elt {
    elt(int _c, intvar _x)
      : c(_c), x(_x) { }
    int c;
    intvar x;
  };

  forceinline int delta(int c, pid_t p) {
    return c * (s->state.p_vals[p] - s->wake_vals[p]);
  }

  int compute_lb(void) {
    int lb = 0;
    for(const elt& e : xs)
      lb += e.c * e.x.lb(s);
    return lb;
  }

  watch_result wake_r(int xi) {
    trail_change(s->persist, status, (char) S_Active);

    // Compute the threshold
    int new_threshold = 0;
    for(const elt& e : xs)
      new_threshold = std::max(new_threshold, (int) (e.c * (e.x.ub(s) - e.x.lb(s))));
    if(slack < new_threshold) {
      queue_prop();
    } else {
//      trail_change(s->persist, threshold, new_threshold);
      set(threshold, new_threshold);
    }
    return Wt_Keep;
  }

  watch_result wake_x(int xi) {
    if(status&S_Red)
      return Wt_Keep;

    trail_change(s->persist, slack, slack - delta(xs[xi].c, xs[xi].x.p));
#ifdef CHECK_STATE
    // Might not have processed all watches yet
    assert(slack >= k - compute_lb());
#endif
    if(slack < threshold)
      queue_prop();
    return Wt_Keep;
  }

  // Requires backtracking
  void ex_naive(int ei, vec<clause_elt>& expl) {
    for(int xi = 0; xi < xs.size(); xi++) {
      if(xi == ei)
        continue;
      expl.push(xs[xi].x < xs[xi].x.lb(s));
    }
  }

  void ex_r(int ex_slack, vec<clause_elt>& expl) {
    make_expl(Var_None, ex_slack, expl);
  }

  void ex_x(int xi, pval_t pval, vec<clause_elt>& expl) {
#ifndef EXPL_NAIVE
    intvar::val_t ival(xs[xi].x.ub_of_pval(pval));
    intvar::val_t lim(k - xs[xi].c*(ival+1) + 1);

    intvar::val_t sum = 0;
    for(int xj : irange(xi))
      sum += xs[xj].c * xs[xj].x.lb(s);
    for(int xj : irange(xi+1, xs.size()))
      sum += xs[xj].c * xs[xj].x.lb(s);
    expl.push(~r);
    make_expl(xi, sum - lim, expl);
#else
    // Naive explanation
    expl.push(~r);
    for(elt e : xs) {
      assert(s->state.is_inconsistent(e.x < e.x.lb(s)));
      expl.push(e.x < e.x.lb(s));
    }
#endif
  }


  public: 

    lin_le_inc(solver_data* s, patom_t _r, vec<int>& ks, vec<intvar>& vs, int _k)
      : propagator(s), r(_r), k(_k), slack(k), threshold(0), status(0)
      {
      for(int ii = 0; ii < vs.size(); ii++) {
        elt e = ks[ii] > 0 ? elt(ks[ii], vs[ii]) : elt(-ks[ii], -vs[ii]);
        e.x.attach(E_LB, watch<&P::wake_x>(xs.size(), Wt_IDEM));
        xs.push(e);
      }
      // Initialize lower bound
      for(const elt& e : xs)
        slack -= e.c * lb_prev(e.x);
      // Tighten upper bound, and compute threshold? 
      if(s->state.is_entailed(r)) {
        status = S_Active;
        for(elt& e : xs) {
          int x_ub = e.x.lb(s) + slack/e.c;
          if(x_ub < e.x.ub(s))
            set_ub(e.x, x_ub, reason());
          // threshold = std::max(threshold, (int) (e.c * (e.x.ub(s) - e.x.lb_prev())));
          threshold.x = std::max(threshold.x, (int) (e.c * (e.x.ub(s) - lb_prev(e.x))));
        }
        assert(slack >= k - compute_lb());
      } else {
        attach(s, r, watch<&P::wake_r>(0, Wt_IDEM));
        for(elt& e : xs) {
          int x_ub = e.x.lb(s) + slack/e.c;
          if(x_ub < e.x.ub(s))
            add_clause(s, ~r, e.x <= x_ub);
        }
        threshold.x = 0;
      }
    }

    void root_simplify(void) {
        
    }
    
    template<class E>
    void make_expl(int var, int slack, E& ex) {
      assert(slack >= 0);

#if 0
      for(int xi = xs.size()-1; xi >= 0; --xi) {
        if(xi == var)
          continue;
        elt e = xs[xi];

        int x_lb = lb(e.x);
        int x_lb_prev = lb_prev(e.x);

        int diff = e.c * (x_lb - x_lb_prev);
        if(diff <= slack) {
          slack -= diff;

          diff = e.c * (x_lb_prev - lb_0(e.x));
          if(diff <= slack) {
            slack -= diff;
            continue;
          }
          ex.push(e.x < x_lb_prev); 
          continue;
        }
        ex.push(e.x < x_lb);
      }
#else
      // First, collect things we can omit entirely, or
      // include at the previous decision level
      vec<int> xs_pending;
      for(int xi : irange(0, xs.size())) {
        if(xi == var)
          continue;
        elt e = xs[xi];

        int x_lb = e.x.lb(s);
        int x_lb_0 = lb_0(e.x);
        int diff_0 = e.c * (x_lb - x_lb_0);
        if(diff_0 <= slack) {
          slack -= diff_0;
          continue;
        }
        xs_pending.push(xi);
      }

      int* xp = xs_pending.begin();
      for(int xi : xs_pending) {
        elt e = xs[xi];
        int x_lb = e.x.lb(s);
        int x_lb_p = lb_prev(e.x);
        int diff_p = e.c * (x_lb - x_lb_p);
        if(diff_p <= slack) {
          slack -= diff_p;
          ex.push(e.x < x_lb_p); 
          continue;
        }
        *xp = xi; ++xp;
      }
      xs_pending.shrink_(xs_pending.end() - xp);

      // Then, add things at the current level
      assert(slack >= 0);
      for(int xi : xs_pending) {
        elt e = xs[xi];
        int diff = slack/e.c;
        ex.push(e.x < e.x.lb(s) - diff);
        slack -= e.c * diff;
        assert(slack >= 0);
      }
#endif
    }

    bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_PROP
      std::cout << "[[Running linear_le(inc)]]" << std::endl;
#endif
#ifdef CHECK_STATE
      assert(slack == k - compute_lb());
#endif
      /*
      static unsigned int count = 0;
      static unsigned int lim = 1000;
      */

      if(status&S_Red)
        return false;

      if(slack < 0) {
        // Collect enough atoms to explain the sum.
        // FIXME: This is kinda weak. We really want to
        // push as much as we can onto the previous level.
        if(!enqueue(*s, ~r, ex_thunk(ex_nil<&P::ex_r>, -slack-1, expl_thunk::Ex_BTPRED)))
          return false;
        trail_change(s->persist, status, (char) S_Red);
        return true;
#ifdef CHECK_STATE
//        assert(confl_is_current(s, confl));
#endif
      }

      if(!(status&S_Active))
        return true;

      /*
      if(++count > lim) {
        fprintf(stderr, "lin_le_inc: %d\n", count);
        lim *= 1.1;
      }
      */

      // Otherwise, propagate upper bounds.
//      int slack = k - lb;
      int new_threshold = 0;
      for(int xi : irange(0, xs.size())) {
        elt e = xs[xi];
        int x_diff = slack/e.c;
        int x_ub = e.x.lb(s) + x_diff;
        if(x_ub < e.x.ub(s)) {
          // Build the explanation
          if(!set_ub(e.x, x_ub,
              ex_thunk(ex<&P::ex_x>, xi, expl_thunk::Ex_BTPRED)))
            return false;
        }
        new_threshold = std::max(new_threshold, (int) (e.c * (e.x.ub(s) - e.x.lb(s))));
      }

      // trail_change(s->persist, threshold, new_threshold);
      set(threshold, new_threshold);
      return true;
    }

    patom_t r;
    vec<elt> xs;
    int k;

    // Persistent state
    int slack;
    // int threshold;
    Tint threshold;
    char status;
};

// Linear propagator, which uses an implicit tree to track partial sums.
// The tree isn't trailed; instead, it's re-initialized after backtracking.
class lin_le_tree : public propagator, public prop_inst<lin_le_tree> {
  enum { Var_None = -1 };
  enum { S_None = 0, S_Active = 1, S_Red = 2 };

  // Now many total nodes do we need for a complete tree with n leaves?
  unsigned int TREE_SZ(unsigned int nodes) { return (1<<(33 - __builtin_clz(nodes-1))) - 1; }
  // Navigating the implicit tree.
  unsigned int PARENT(unsigned int p) { return (p-1)>>1; }
  unsigned int LEFT(unsigned int p) { return (p<<1)+1; }
  unsigned int RIGHT(unsigned int p) { return (p<<1)+2; }
  bool IS_LEFT(unsigned int p) { return p&1; }
  bool IS_RIGHT(unsigned int p) { return !(p&1); }
  unsigned int SIB(unsigned int p) { return IS_LEFT(p) ? p+1 : p-1; }
  
  struct elt {
    typedef int val_t;

    elt(int _c, intvar _x)
      : c(_c), x(_x) { }
    int c;
    intvar x;

    int lb(ctx_t& ctx) const { return c * x.lb(ctx); }
    int ub(ctx_t& ctx) const { return c * x.ub(ctx); }
  };

  // Don't need to propagate so long as nodes[0].limit <= k.
  struct ps_node {
    int lb;    // Lower bound of variables above here.
    int limit; // Max value of one-ub plus the remaining lbs.
  };

  bool init_ps(void) {
    // Initialize leaves.
    assert(!ps_current);
    int max = 0;

    ctx_t& ctx(s->state.p_vals);
    ps_node* n = nodes+base;
    for(int xi = 0; xi < xs.size(); ++xi, ++n) {
      max += xs[xi].ub(ctx);
      (*n) = { xs[xi].lb(ctx), xs[xi].ub(ctx) };
    }

    // If the constraint is definitely satisfied, stop.
    if(max <= k) {
      trail_change(s->persist, status, (char) S_Red);
      return false;
    }

    for(int pi = base-1; pi >= 0; --pi) {
      nodes[pi] = {
        nodes[LEFT(pi)].lb + nodes[RIGHT(pi)].lb,
        std::max(nodes[LEFT(pi)].lb + nodes[RIGHT(pi)].limit, nodes[LEFT(pi)].limit + nodes[RIGHT(pi)].lb)
      };
    }

    // Make sure this is invalidated upon backtracking. 
    ps_current = true;
    s->persist.bt_flags.push(&ps_current);  
    return true;
  }

  // Update idx_of(xi), and all parents.
  void update_ps(unsigned int xi) {
    if(!ps_current) {
      init_ps();
      return;
    }
    unsigned int pi = base + xi;
    
    int p_lb = lb(xs[xi]);
    nodes[pi].lb = p_lb;
    while(pi) {
      unsigned int par = PARENT(pi);
      int par_lb = p_lb + nodes[SIB(pi)].lb;
      int par_lim = std::max(nodes[par].limit, p_lb + nodes[SIB(pi)].limit);
      nodes[par] = { par_lb, par_lim };
      
      pi = par;
      p_lb = par_lb;
    }
  }

  forceinline int delta(int c, pid_t p) {
    return c * (s->state.p_vals[p] - s->wake_vals[p]);
  }

  int compute_lb(void) {
    int lb = 0;
    for(const elt& e : xs)
      lb += e.c * e.x.lb(s);
    return lb;
  }

  watch_result wake_r(int xi) {
    // If init_ps() returns false, don't bother.
    if(status&S_Red)
      return Wt_Keep;

    if(init_ps()) {
      trail_change(s->persist, status, (char) S_Active);
      if(nodes[0].limit > k)
        queue_prop();
    }
    return Wt_Keep;
  }

  watch_result wake_x(int xi) {
    if(status&S_Red)
      return Wt_Keep;
    
    if(status&S_Active) {
      update_ps(xi);
      if(nodes[0].limit > k)
        queue_prop();
    } else {
      int diff = delta(xs[xi].c, xs[xi].x.p);
      slack.set(s->persist, slack - diff);
      if(slack < 0)
        queue_prop();
    }
    return Wt_Keep;
  }

  void ex_r(int ex_slack, vec<clause_elt>& expl) {
    make_expl(Var_None, ex_slack, expl);
  }

  void ex_x(int xi, pval_t pval, vec<clause_elt>& expl) {
    intvar::val_t ival(xs[xi].x.ub_of_pval(pval));
    intvar::val_t lim(k - xs[xi].c*(ival+1) + 1);

    intvar::val_t sum = 0;
    for(int xj : irange(xi))
      sum += lb(xs[xj]);
    for(int xj : irange(xi+1, xs.size()))
      sum += lb(xs[xj]);
    expl.push(~r);
    make_expl(xi, sum - lim, expl);
  }

  public: 
    lin_le_tree(solver_data* s, patom_t _r, vec<int>& ks, vec<intvar>& vs, int _k)
      : propagator(s), r(_r), k(_k)
      , nodes((ps_node*) malloc(sizeof(ps_node) * TREE_SZ(vs.size()))), base(TREE_SZ(vs.size())/2)
      , ps_current(0)
      , slack(k), status(0)
      {
      for(int ii = 0; ii < vs.size(); ii++) {
        int c = ks[ii];
        intvar x = vs[ii];
        if(c < 0) {
          c = -c;
          x = -x;
        }
        int x_lb = lb_prev(x);
        if(x_lb != 0) {
          k -= c * x_lb;
          x -= x_lb;
        }
        elt e = elt(c, x);
        x.attach(E_LB, watch<&P::wake_x>(xs.size(), Wt_IDEM));
        xs.push(e);
      }
      for(int pi = base + vs.size(); pi < TREE_SZ(vs.size()); ++pi) {
        nodes[pi] = { 0, 0 };
      }
      
      // Initialize lower bound
      slack.x = k;
      if(s->state.is_entailed(r)) {
        // Already active
        assert(k >= 0);
        status = S_Active;
        init_ps();
      } else {
        if(k < 0) {
          enqueue(*s, ~r, reason());
          status = S_Red;
        } else {
          attach(s, r, watch<&P::wake_r>(0, Wt_IDEM));
        }
      }
    }

    ~lin_le_tree(void) {
      free(nodes);
    }

    void root_simplify(void) {
      // Do stuff?   
    }
    
    template<class E>
    void make_expl(int var, int slack, E& ex) {
      assert(slack >= 0);
      // First, collect things we can omit entirely, or
      // include at the previous decision level
      vec<int> xs_pending;
      for(int xi : irange(0, xs.size())) {
        if(xi == var)
          continue;
        elt e = xs[xi];

        int x_lb = e.x.lb(s);
        int x_lb_0 = lb_0(e.x);
        int diff_0 = e.c * (x_lb - x_lb_0);
        if(diff_0 <= slack) {
          slack -= diff_0;
          continue;
        }
        xs_pending.push(xi);
      }

      int* xp = xs_pending.begin();
      for(int xi : xs_pending) {
        elt e = xs[xi];
        int x_lb = e.x.lb(s);
        int x_lb_p = lb_prev(e.x);
        int diff_p = e.c * (x_lb - x_lb_p);
        if(diff_p <= slack) {
          slack -= diff_p;
          ex.push(e.x < x_lb_p); 
          continue;
        }
        *xp = xi; ++xp;
      }
      xs_pending.shrink_(xs_pending.end() - xp);

      // Then, add things at the current level
      assert(slack >= 0);
      for(int xi : xs_pending) {
        elt e = xs[xi];
        int diff = slack/e.c;
        ex.push(e.x < e.x.lb(s) - diff);
        slack -= e.c * diff;
        assert(slack >= 0);
      }
    }

    bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_PROP
      std::cout << "[[Running linear_le(tree)]]" << std::endl;
#endif
      /*
      static unsigned int count = 0;
      static unsigned int lim = 1000;
      */

      if(status&S_Red)
        return true;

      if(slack < 0) {
        if(!enqueue(*s, ~r, ex_thunk(ex_nil<&P::ex_r>, -slack-1, expl_thunk::Ex_BTPRED)))
          return false;
        trail_change(s->persist, status, (char) S_Red);
        return true;
      }

      if(!(status&S_Active))
        return true;
      
      /*
      if(++count > lim) {
        fprintf(stderr, "lin_le_tree: %d\n", count);
        lim *= 1.1;
      }
      */
      // Propagate the ps_tree
      if(nodes[0].lb > k) { 
        confl.push(~r);
        make_expl(Var_None, nodes[0].lb - k - 1, confl);
        return false;
      }
      if(!prop_ps(0, k))
        return false;

      return true;
    }

    bool prop_ps(unsigned int pi, int cap) {
      if(nodes[pi].limit <= cap)
        return true;

      if(pi < base) {
        // Not at a leaf, yet.
        if(!prop_ps(LEFT(pi), cap - nodes[RIGHT(pi)].lb))
          return false;
        if(!prop_ps(RIGHT(pi), cap - nodes[LEFT(pi)].lb))
          return false;
        nodes[pi].limit = std::max(nodes[LEFT(pi)].lb + nodes[RIGHT(pi)].limit,
                                  nodes[LEFT(pi)].limit + nodes[RIGHT(pi)].lb);
      } else {
        int xi = pi - base;
        int x_ub = cap/xs[xi].c;
        if(x_ub < ub(xs[xi].x)) {
          if(!set_ub(xs[xi].x, x_ub, ex_thunk(ex<&P::ex_x>, xi, expl_thunk::Ex_BTPRED)))
            return false;
          nodes[pi].limit = xs[xi].c * x_ub;
        } else {
          nodes[pi].limit = ub(xs[xi]);
        }
      }
      return true;
    }

    patom_t r;
    vec<elt> xs;
    int k;
    
    // Semi-transient state: rebuilt on the first wakeup after backtracking.
    ps_node* nodes;
    unsigned int base;
    char ps_current;

    // Persistent state
    Tint slack;
    char status;
};

#if 0
class lin_le_tree_ps : public propagator, public prop_inst<lin_le_tree_ps> {
  enum { Var_None = -1 };
  enum { S_None = 0, S_Active = 1, S_Red = 2 };

  // Now many total nodes do we need for a complete tree with n leaves?
  unsigned int TREE_SZ(unsigned int nodes) { return (1<<(33 - __builtin_clz(nodes-1))) - 1; }
  // Navigating the implicit tree.
  unsigned int PARENT(unsigned int p) { return (p-1)>>1; }
  unsigned int LEFT(unsigned int p) { return (p<<1)+1; }
  unsigned int RIGHT(unsigned int p) { return (p<<1)+2; }
  bool IS_LEFT(unsigned int p) { return p&1; }
  bool IS_RIGHT(unsigned int p) { return !(p&1); }
  unsigned int SIB(unsigned int p) { return IS_LEFT(p) ? p+1 : p-1; }
  
  struct elt {
    typedef int val_t;

    elt(int _c, intvar _x)
      : c(_c), x(_x) { }
    int c;
    intvar x;

    int lb(ctx_t& ctx) const { return c * x.lb(ctx); }
    int ub(ctx_t& ctx) const { return c * x.ub(ctx); }
  };

  // Don't need to propagate so long as nodes[0].limit <= k.
  struct ps_node {
    int lb;    // Lower bound of variables above here.
    int limit; // Max value of one-ub plus the remaining lbs.
  };

  bool init_ps(void) {
    // Initialize leaves.
    assert(!ps_current);
    int max = 0;

    ctx_t& ctx(s->state.p_vals);
    ps_node* n = nodes+base;
    for(int xi = 0; xi < xs.size(); ++xi, ++n) {
      max += xs[xi].ub(ctx);
      (*n) = { xs[xi].lb(ctx), xs[xi].ub(ctx) };
    }

    // If the constraint is definitely satisfied, stop.
    if(max <= k) {
      trail_change(s->persist, status, (char) S_Red);
      return false;
    }

    for(int pi = base-1; pi >= 0; --pi) {
      nodes[pi] = {
        nodes[LEFT(pi)].lb + nodes[RIGHT(pi)].lb,
        std::max(nodes[LEFT(pi)].lb + nodes[RIGHT(pi)].limit, nodes[LEFT(pi)].limit + nodes[RIGHT(pi)].lb)
      };
    }

    // Make sure this is invalidated upon backtracking. 
    ps_current = true;
    s->persist.bt_flags.push(&ps_current);  
    return true;
  }

  // Update idx_of(xi), and all parents.
  void update_ps(unsigned int xi) {
    if(!ps_current) {
      init_ps();
      return;
    }
    unsigned int pi = base + xi;
    
    int p_lb = lb(xs[xi]);
    nodes[pi].lb = p_lb;
    while(pi) {
      unsigned int par = PARENT(pi);
      int par_lb = p_lb + nodes[SIB(pi)].lb;
      int par_lim = std::max(nodes[par].limit, p_lb + nodes[SIB(pi)].limit);
      nodes[par] = { par_lb, par_lim };
      
      pi = par;
      p_lb = par_lb;
    }
  }

  bool update_ps_preds(unsigned int xi) {
    // Partial sums are only updated when
    // the variable is fixed.
    unsigned int pi = base + xi;

    int x_lb = lb(xs[xi]);
    while(pi) {
      pi = PARENT(pi); 
      pid_t p = ps_preds[pi];
      pval_t v = std::min(k+1, pred_lb(s, p) + x_lb);
      if(!enqueue(*s, ge_atom(p, v), ex_thunk(ex<&P::ex_ps>, pi, expl_thunk::Ex_BTPRED)))
        return false;
    }
    return true;
  }

  forceinline int delta(int c, pid_t p) {
    return c * (s->state.p_vals[p] - s->wake_vals[p]);
  }

  int compute_lb(void) {
    int lb = 0;
    for(const elt& e : xs)
      lb += e.c * e.x.lb(s);
    return lb;
  }

  watch_result wake_r(int xi) {
    // If init_ps() returns false, don't bother.
    if(status&S_Red)
      return Wt_Keep;

    if(init_ps()) {
      trail_change(s->persist, status, (char) S_Active);
      if(nodes[0].limit > k)
        queue_prop();
    }
    return Wt_Keep;
  }

  watch_result wake_x(int xi) {
    if(status&S_Red)
      return Wt_Keep;
    
    if(status&S_Active) {
      update_ps(xi);
      if(nodes[0].limit > k)
        queue_prop();
    } else {
      int diff = delta(xs[xi].c, xs[xi].x.p);
      slack.set(s->persist, slack - diff);
      if(slack < 0)
        queue_prop();
    }
    return Wt_Keep;
  }

  watch_result wake_fix_x(int xi) {
    if(status&S_Red)
      return Wt_Keep;
    fixed_xs.push(xi);
    queue_prop(); 
    return Wt_Keep;
  }

  void ex_r(int ex_slack, vec<clause_elt>& expl) {
    make_expl(Var_None, ex_slack, expl);
  }

  void ex_x(int xi, pval_t pval, vec<clause_elt>& expl) {
    intvar::val_t ival(xs[xi].x.ub_of_pval(pval));
    intvar::val_t lim(k - xs[xi].c*(ival+1) + 1);

    intvar::val_t sum = 0;
    for(int xj : irange(xi))
      sum += lb(xs[xj]);
    for(int xj : irange(xi+1, xs.size()))
      sum += lb(xs[xj]);
    expl.push(~r);
    make_expl(xi, sum - lim, expl);
  }

  void ex_ps(int pi, pval_t pval, vec<clause_elt>& expl) {
    if(pi < base) {
      // 
    } else {
      int xi = pi - base;
      expl.push(xs[xi].x < pval/xs[xi].c);
    }
  }

  public: 
    lin_le_tree(solver_data* s, patom_t _r, vec<int>& ks, vec<intvar>& vs, int _k)
      : propagator(s), r(_r), k(_k)
      , nodes((ps_node*) malloc(sizeof(ps_node) * TREE_SZ(vs.size()))), base(TREE_SZ(vs.size())/2)
      , ps_current(0)
      , slack(k), status(0)
      {
      for(int ii = 0; ii < vs.size(); ii++) {
        int c = ks[ii];
        intvar x = vs[ii];
        if(c < 0) {
          c = -c;
          x = -x;
        }
        int x_lb = lb_prev(x);
        if(x_lb != 0) {
          k -= c * x_lb;
          x -= x_lb;
        }
        elt e = elt(c, x);
        x.attach(E_LB, watch<&P::wake_x>(xs.size(), Wt_IDEM));
        xs.push(e);
      }
      for(int pi = base + vs.size(); pi < TREE_SZ(vs.size()); ++pi) {
        nodes[pi] = { 0, 0 };
      }
      
      // Initialize lower bound
      slack.x = k;

      // And partial sums.
      ps_preds = malloc(sizeof(pid_t) * base);
      for(int ii = 0; ii < ps_preds; ii++)
        ps_preds[ii] = new_pred(*s, 0, k+1, PR_NOBRANCH);

      if(s->state.is_entailed(r)) {
        // Already active
        assert(k >= 0);
        status = S_Active;
        init_ps();
      } else {
        if(k < 0) {
          enqueue(*s, ~r, reason());
          status = S_Red;
        } else {
          attach(s, r, watch<&P::wake_r>(0, Wt_IDEM));
        }
      }
    }

    ~lin_le_tree(void) {
      free(nodes);
    }

    void root_simplify(void) {
      // Do stuff?   
    }

    void cleanup(void) {
      in_queue = false;
      fixed_xs.clear();
    }
    
    template<class E>
    void make_expl(int var, int slack, E& ex) {
      assert(slack >= 0);
      // First, collect things we can omit entirely, or
      // include at the previous decision level
      vec<int> xs_pending;
      for(int xi : irange(0, xs.size())) {
        if(xi == var)
          continue;
        elt e = xs[xi];

        int x_lb = e.x.lb(s);
        int x_lb_0 = lb_0(e.x);
        int diff_0 = e.c * (x_lb - x_lb_0);
        if(diff_0 <= slack) {
          slack -= diff_0;
          continue;
        }
        xs_pending.push(xi);
      }

      int* xp = xs_pending.begin();
      for(int xi : xs_pending) {
        elt e = xs[xi];
        int x_lb = e.x.lb(s);
        int x_lb_p = lb_prev(e.x);
        int diff_p = e.c * (x_lb - x_lb_p);
        if(diff_p <= slack) {
          slack -= diff_p;
          ex.push(e.x < x_lb_p); 
          continue;
        }
        *xp = xi; ++xp;
      }
      xs_pending.shrink_(xs_pending.end() - xp);

      // Then, add things at the current level
      assert(slack >= 0);
      for(int xi : xs_pending) {
        elt e = xs[xi];
        int diff = slack/e.c;
        ex.push(e.x < e.x.lb(s) - diff);
        slack -= e.c * diff;
        assert(slack >= 0);
      }
    }

    bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_PROP
      std::cout << "[[Running linear_le(tree)]]" << std::endl;
#endif
      /*
      static unsigned int count = 0;
      static unsigned int lim = 1000;
      */

      if(status&S_Red)
        return true;

      if(slack < 0) {
        if(!enqueue(*s, ~r, ex_thunk(ex_nil<&P::ex_r>, -slack-1, expl_thunk::Ex_BTPRED)))
          return false;
        trail_change(s->persist, status, (char) S_Red);
        return true;
      }

      if(!(status&S_Active))
        return true;
      
      /*
      if(++count > lim) {
        fprintf(stderr, "lin_le_tree: %d\n", count);
        lim *= 1.1;
      }
      */
      // Propagate the ps_tree
      if(!prop_ps(0, k))
        return false;

      for(unsigned int xi : fixed_xs) {
        if(!update_ps_preds(xi))
          return false;
      }
      fixed_xs.clear();

      return true;
    }

    bool prop_ps(unsigned int pi, int cap) {
      if(nodes[pi].limit <= cap)
        return true;

      if(pi < base) {
        // Not at a leaf, yet.
        if(!prop_ps(LEFT(pi), cap - nodes[RIGHT(pi)].lb))
          return false;
        if(!prop_ps(RIGHT(pi), cap - nodes[LEFT(pi)].lb))
          return false;
        nodes[pi].limit = std::max(nodes[LEFT(pi)].lb + nodes[RIGHT(pi)].limit,
                                  nodes[LEFT(pi)].limit + nodes[RIGHT(pi)].lb);
      } else {
        int xi = pi - base;
        int x_ub = cap/xs[xi].c;
        if(x_ub < ub(xs[xi].x)) {
          if(!set_ub(xs[xi].x, x_ub, ex_thunk(ex<&P::ex_x>, xi, expl_thunk::Ex_BTPRED)))
            return false;
          nodes[pi].limit = xs[xi].c * x_ub;
        } else {
          nodes[pi].limit = ub(xs[xi]);
        }
      }
      return true;
    }

    patom_t r;
    vec<elt> xs;
    int k;
    
    // Semi-transient state: rebuilt on the first wakeup after backtracking.
    ps_node* nodes;
    pid_t* ps_preds;
    unsigned int base;
    char ps_current;

    // Transient state
    vec<unsigned int> fixed_xs;

    // Persistent state
    Tint slack;
    char status;
};
#endif

class int_linear_ne : public propagator, public prop_inst<int_linear_ne> {
  enum { Var_None = 0, Var_LB = 1, Var_UB = 2 };
  enum { S_Active = 1, S_Red = 2 };

  enum TrigKind { T_Atom, T_Var };
  struct trigger {
    TrigKind kind;
    unsigned int idx;
  };
  
  inline bool is_triggered(trigger t) {
    switch(t.kind) {
      case T_Atom:
        return s->state.is_entailed(r);
      case T_Var:
        return vs[t.idx].x.is_fixed(s);
      default:
        ERROR;
        return false;
    }
  }

  inline void attach_trigger(trigger t, int ii) {
    switch(t.kind) {
      case T_Atom:
        attach(s, r, watch<&P::wake_trig>(ii, Wt_IDEM));
        break;
      case T_Var:
        vs[t.idx].x.attach(E_FIX, watch<&P::wake_trig>(ii, Wt_IDEM));
        break;
    }
  }

  // See if we can find some other unfixed variable
  watch_result wake_bound(int vi) {
    if(!(status&S_Active) || !is_triggered(trigs[1 - t_act]))
      return Wt_Drop;

    queue_prop();
    return Wt_Keep;
  }

  watch_result wake_trig(int ti) {
    // Look for a replacement watch
    for(int ii = 2; ii < trigs.size(); ii++) {
      if(!is_triggered(trigs[ii])) {
        std::swap(trigs[ti], trigs[ii]);
        attach_trigger(trigs[ti], ti);  
        return Wt_Drop;
      }
    }
    // None found
    if(!is_triggered(trigs[1 - ti]))
      t_act = 1 - ti;
    queue_prop();
    return Wt_Keep;
  }

  inline void ex_trig(trigger t, vec<clause_elt>& expl) {
    switch(t.kind) {
      case T_Atom:
        expl.push(~r);
        return;
      case T_Var:
      /*
        expl.push(vs[t.idx].x < vs[t.idx].x.lb(s));
        expl.push(vs[t.idx].x > vs[t.idx].x.ub(s)); 
        */
        expl.push(vs[t.idx].x != vs[t.idx].x.lb(s));
        return;
    }
  }

  void expl(int xi, vec<clause_elt>& expl) {
    ex_trig(trigs[1 - t_act], expl);
    for(int ti = 2; ti < trigs.size(); ti++)
      ex_trig(trigs[ti], expl);

    if(xi&E_LB)
      expl.push(vs[t_act].x < excl_val);
    if(xi&E_UB)
      expl.push(vs[t_act].x > excl_val);
  }

public:
  struct elt {
    elt(int _c, intvar _x)
      : c(_c), x(_x) { }
    int c;
    intvar x;
  };
  
  int_linear_ne(solver_data* s, patom_t _r, vec<int>& ks, vec<intvar>& xs, int _k)
    : propagator(s), r(_r), k(_k), t_act(0), status(0) {
    assert(xs.size() >= 2);
    for(int ii = 0; ii < xs.size(); ii++) {
      // FIXME
      make_eager(xs[ii]);
      vs.push(elt { ks[ii], xs[ii] });
      trigs.push(trigger { T_Var, (unsigned int) ii });
    }
    if(!s->state.is_entailed(r)) {
      trigger t(trigs[0]);
      trigs.push(t);
      trigs[0] = { T_Atom };
    }
    attach_trigger(trigs[0], 0);
    attach_trigger(trigs[1], 1);
  }

  bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_PROP
    std::cout << "[[Running linear_ne]]" << std::endl;
#endif
    if(status&S_Active) {
      int idx = trigs[t_act].idx;
      if(vs[idx].x.lb(s) == excl_val) {
        return set_lb(vs[idx].x, excl_val+1, ex_thunk(ex_nil<&P::expl>, E_LB));
      } else {
        assert(vs[idx].x.ub(s) == excl_val);
        return set_ub(vs[idx].x, excl_val-1, ex_thunk(ex_nil<&P::expl>, E_UB));
      }
    }

    if(trigs[t_act].kind == T_Atom) {
      intvar::val_t sum = k;
      for(const elt& e : vs)
        sum -= e.c * e.x.lb(s);

      if(sum)
        return true;
      return enqueue(*s, ~r, ex_thunk(ex_nil<&P::expl>, 0));
    } else {
      int vi = trigs[t_act].idx;
      intvar::val_t sum = k;
      for(int ii = 0; ii < vi; ii++)
        sum -= vs[ii].c * vs[ii].x.lb(s);
      for(int ii = vi+1; ii < vs.size(); ii++)
        sum -= vs[ii].c * vs[ii].x.lb(s);

      if(sum % vs[vi].c != 0)
        return true;
      
      // Check if it's already satisfied or propagatable.
      excl_val = sum/vs[vi].c;   
#if 0
      if(vs[vi].x.lb(s) >= excl_val) {
        if(vs[vi].x.lb(s) == excl_val)
          return set_lb(vs[vi].x,excl_val+1, ex_thunk(ex_nil<&P::expl>, E_LB));
        return true;
      } else if(vs[vi].x.ub(s) <= excl_val) {
        if(vs[vi].x.ub(s) == excl_val)
          return set_lb(vs[vi].x,excl_val-1, ex_thunk(ex_nil<&P::expl>, E_UB));
        return true;
      }
      
      // Otherwise, add the new watches
      trail_change(s->persist, status, (char) S_Active);
      attach(s, vs[vi].x >= excl_val, watch<&P::wake_bound>(0, Wt_IDEM));
      attach(s, vs[vi].x <= excl_val, watch<&P::wake_bound>(1, Wt_IDEM));
      return true;
#else
      if(vs[vi].x.lb(s) > excl_val)
        return true;
      if(vs[vi].x.ub(s) < excl_val)
        return true;
      return enqueue(*s, vs[vi].x != excl_val, ex_thunk(ex_nil<&P::expl>, 0));
#endif
    }
    return true;
  }

  // virtual bool check_sat(void) { return true; }
  // void root_simplify(void) { }
  patom_t r;

  vec<elt> vs;
  int k;

  vec<trigger> trigs;
  unsigned int t_act;
  char status;
  intvar::val_t excl_val;
};

struct term {
  int k;
  intvar x;

  int lb(solver_data* s) const { return k * x.lb(s); }
  int ub(solver_data* s) const { return k * x.ub(s); }
};

intvar make_ps(solver_data* s, patom_t r, term tx, term ty, int k) {
  int ub = std::min(k, tx.ub(s) + ty.ub(s));
  intvar ps = new_intvar(s, 0, ub);
  vec<int> ks { tx.k, ty.k, -1 };
  vec<intvar> xs { tx.x, ty.x, ps };
  lin_le_inc::post(s, r, ks, xs, 0);
  return ps;
}
bool linear_le_chain(solver_data* s, patom_t r, vec<int>& ks, vec<intvar>& vs, int k) {
  if(ks.size() <= 2) {
    lin_le_inc::post(s, r, ks, vs, k);
    return true;
  }
  // Normalize the terms, correcting for lower bounds.
  vec<term> xs;
  for(int ii = 0; ii < ks.size(); ii++) {
    term t = ks[ii] < 0 ? term { -ks[ii], -vs[ii] } : term { ks[ii], vs[ii] }; 
    int low = t.x.lb(s);
    t.x -= low;
    k -= t.k * low;
    xs.push(t);
  }
  if(k < 0)
    return false;
  
  /*
  if(xs.size() <= 2) {
    vec<int> o_ks; vec<intvar> o_vs;    
    for(term t : xs) {
      o_ks.push(t.k);
      o_vs.push(t.x);
    }
    new lin_le_inc(s, r, o_ks, o_vs, k);
    return true;
  }
  */
  intvar ps = make_ps(s, r,  xs[0], xs[1], k);
  for(int ii = 2; ii < xs.size() -1; ii++) {
    ps = make_ps(s, r, term { 1, ps }, xs[ii], k);
  }
  vec<int> o_ks { 1, xs.last().k };
  vec<intvar> o_xs { ps, xs.last().x };
  return lin_le_inc::post(s, r, o_ks, o_xs, k);
}

bool linear_le(solver_data* s, vec<int>& ks, vec<intvar>& vs, int k,
  patom_t r) {
  /*
  if(!s->state.is_entailed_l0(r)) {
    WARN("Half-reification not yet implemented for linear_le.");
  }
  */
//   new int_linear_le(s, r, ks, vs, k);
#ifndef USE_CHAIN
  // new lin_le_inc(s, r, ks, vs, k);
  // new lin_le_tree(s, r, ks, vs, k);
  // return true;

  // return int_linear_le::post(s, r, ks, vs, k);
  return lin_le_inc::post(s, r, ks, vs, k);
  // return lin_le_tree::post(s, r, ks, vs, k);
#else
  return linear_le_chain(s, r, ks, vs, k);
#endif
}

bool linear_ne(solver_data* s, vec<int>& ks, vec<intvar>& vs, int k,
  patom_t r) {
  /*
  if(!s->state.is_entailed_l0(r)) {
    // WARN("Half-reification not yet implemented for linear_ne.");
    WARN("Half-reified linear_ne is a bit of a hack.");
    patom_t a = new_bool(*s);
    patom_t b = new_bool(*s);
    add_clause(s, ~r, a, b);
    new int_linear_le(s, a, ks, vs, k-1);
    vec<int> neg_ks;
    for(int k : ks)
      neg_ks.push(-k);
    new int_linear_le(s, b, neg_ks, vs, -k+1);
  } else {
    new int_linear_ne(s, r, ks, vs, k);
  }
  */
  // new int_linear_ne(s, r, ks, vs, k);
  // return true;
  return int_linear_ne::post(s, r, ks, vs, k);
}

}
