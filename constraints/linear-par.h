#ifndef GEAS__LINEAR_PAR__H
#define GEAS__LINEAR_PAR__H
#include <cassert>
#include <map>
#include <climits>
#include "mtl/Vec.h"
#include "solver/solver_data.h"
#include "vars/intvar.h"

#include "engine/propagator.h"
#include "engine/propagator_ext.h"

namespace geas {
// Parametric version of the incremental linear inequality
// propagator. To avoid having so much 
#if 0
template<class Wt, class Var>
class lin_leq : public propagator, public prop_inst< lin_leq<Wt, Var> > {
  enum { Var_None = -1 };
  enum { S_Active = 1, S_Red = 2 };
  
  struct elt {
    elt(Wt _c, Var _x)
      : c(_c), x(_x) { }
    Wt c;
    Var x;
  };

  forceinline Wt delta(const elt& e) {
    return e.c * (e.x.lb(s->state.p_vals) - e.x.lb(s->wake_vals));
  }

  Wt compute_lb(void) {
    Wt lb(0);
    for(const elt& e : xs)
      lb += e.c * e.x.lb(s);
    return lb;
  }

  watch_result wake_r(int xi) {
    trail_change(s->persist, status, (char) S_Active);

    // Compute the threshold
    Wt new_threshold = 0;
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

  template<class T>
  inline void EX_PUSH(T& expl, patom_t at) {
    assert(!ub(at));
    expl.push(at);
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
    EX_PUSH(expl, ~r);
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

    lin_leq(solver_data* s, patom_t _r, vec<Wt>& ks, vec<Var>& vs, Wt _k)
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
#ifdef CHECK_STATE
        assert(slack >= k - compute_lb());
#endif
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

      /*
      int* xp = xs_pending.begin();
      for(int xi : xs_pending) {
        elt e = xs[xi];
        int x_lb = e.x.lb(s);
        int x_lb_p = lb_prev(e.x);
        int diff_p = e.c * (x_lb - x_lb_p);
        if(diff_p <= slack) {
          slack -= diff_p;
          EX_PUSH(ex, e.x < x_lb_p); 
          continue;
        }
        *xp = xi; ++xp;
      }
      xs_pending.shrink_(xs_pending.end() - xp);
      */

      // Then, add things at the current level
      assert(slack >= 0);
      for(int xi : xs_pending) {
        elt e = xs[xi];
        int diff = slack/e.c;
        EX_PUSH(ex, e.x < e.x.lb(s) - diff);
        slack -= e.c * diff;
        assert(slack >= 0);
      }
#endif
    }

    bool check_sat(ctx_t& ctx) {
      Wt low(0);
      for(elt e : xs) {
        low += e.c * e.x.lb(ctx);
      }
      return !r.lb(ctx) || low <= k;
    }
    bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); }

    bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_PROP
      std::cout << "[[Running linear_le]]" << std::endl;
#endif
#ifdef CHECK_STATE
      assert(slack == k - compute_lb());
#endif
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
#else
template<class Wt, class Var>
class lin_leq : public propagator, public prop_inst< lin_leq<Wt, Var> > {
public:
  lin_leq(solver_data* s, vec<Wt>& _ks, vec<Var>& _vs, Wt _k, patom_t r = at_True)
    : propagator(s) { }

  bool propagate(vec<clause_elt>& confl) {
    NOT_YET;
    return true;
  }
  void cleanup(void) { }
};

}
#endif
#endif
