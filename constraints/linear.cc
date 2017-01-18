#include <cassert>
#include <map>
#include "mtl/Vec.h"
#include "solver/solver_data.h"
#include "vars/intvar.h"

// #define SKIP_L0
// #define EXPL_EAGER
// #define EXPL_NAIVE

namespace phage {

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
      if(2*xi == ei)
        continue;
      expl.push(xs[xi].x < xs[xi].x.lb());
    }
    for(int yi = 0; yi < ys.size(); yi++) {
      if(2*yi+1 == ei)
        continue;
      expl.push(ys[yi].x > ys[yi].x.ub());
    }
    /*
    for(elt e : p->xs)
      expl.push(e.x < e.x.lb());
    for(elt e : p->ys)
      expl.push(e.x > e.x.ub());
      */
  }

  static void ex_x(void* ptr, int xi, pval_t pval,
                       vec<clause_elt>& expl) {
    int_linear_le* p(static_cast<int_linear_le*>(ptr));
#ifndef EXPL_NAIVE
    intvar::val_t ival(to_int(pval_inv(pval)));
    intvar::val_t lim(p->k - p->xs[xi].c*(ival+1) + 1);

    intvar::val_t sum = 0;
    for(int xj : irange(xi))
      sum += p->xs[xj].c * p->xs[xj].x.lb();
    for(int xj : irange(xi+1, p->xs.size()))
      sum += p->xs[xj].c * p->xs[xj].x.lb();
    for(elt e : p->ys)
      sum -= e.c * e.x.ub();
    p->make_expl(2*xi, sum - lim, expl);
#else
    // Naive explanation
    for(elt e : p->xs) {
      assert(p->s->state.is_inconsistent(e.x < e.x.lb()));
      expl.push(e.x < e.x.lb());
    }
    for(elt e : p->ys) {
      assert(p->s->state.is_inconsistent(e.x > e.x.ub()));
      expl.push(e.x > e.x.ub());
    }
#endif
  }

  static void ex_y(void* ptr, int yi, pval_t pval,
                       vec<clause_elt>& expl) {
    int_linear_le* p(static_cast<int_linear_le*>(ptr));

#ifndef EXPL_NAIVE
    intvar::val_t ival(to_int(pval));
    intvar::val_t lim(p->k + p->ys[yi].c*(ival-1) + 1);

    intvar::val_t sum = 0;
    for(elt e : p->xs)
      sum += e.c * e.x.lb();
    for(int yj : irange(yi))
      sum -= p->ys[yj].c * p->ys[yj].x.ub();
    for(int yj : irange(yi+1, p->ys.size()))
      sum -= p->ys[yj].c * p->ys[yj].x.ub();

    p->make_expl(2*yi+1, sum - lim, expl);
#else
    for(elt e : p->xs) {
      assert(p->s->state.is_inconsistent(e.x < e.x.lb()));
      expl.push(e.x < e.x.lb());
    }
    for(elt e : p->ys) {
      assert(p->s->state.is_inconsistent(e.x > e.x.ub()));
      expl.push(e.x > e.x.ub());
    }
#endif
  }

#ifdef EXPL_EAGER
  static void ex_eager(void* ptr, int pi, pval_t pval,
                       vec<clause_elt>& expl) {
    int_linear_le* p(static_cast<int_linear_le*>(ptr));

    for(patom_t at : p->expls[pi])
      expl.push(at);
  }

  // Allocate a new reason (to be garbage collected)
  int make_eager_expl(int var) {
    trail_push(s->persist, expls_sz);
    int pi = expls_sz++;
    if(expls.size() < expls_sz)
      expls.push();
    vec<patom_t>& expl(expls[pi]);
    expl.clear();

    for(int ii = 0; ii < xs.size(); ii++) {
      if(ii != 2*var) {
        elt e = xs[ii];
        expl.push(e.x < e.x.lb());
      }
    }
    for(int ii = 0; ii < ys.size(); ii++) {
      if(ii != 2*var + 1) {
        elt e = ys[ii];
        expl.push(e.x > e.x.ub());
      }
    }
    
    return pi;
  }
#endif

  public: 

    int_linear_le(solver_data* s, patom_t _r, vec<int>& ks, vec<intvar>& vs, int _k)
      : propagator(s), k(_k)
#ifdef EXPL_EAGER
        , expls_sz(0)
#endif 
      {
      for(int ii = 0; ii < vs.size(); ii++) {
        if(ks[ii] > 0) {
          // vs[ii].attach(E_LB, watch_callback(wake_x, this, xs.size(), true));
          vs[ii].attach(E_LB, watch<&P::wake_x>(xs.size(), Wt_IDEM));
          xs.push(elt(ks[ii], vs[ii]));
        } else if(ks[ii] < 0) {
          // vs[ii].attach(E_UB, watch_callback(wake_y, this, ys.size(), true));
          vs[ii].attach(E_UB, watch<&P::wake_y>(ys.size(), Wt_IDEM));
          ys.push(elt(-ks[ii], vs[ii]));
        }
      }
    }

    void root_simplify(void) {
      
    }
    
    template<class E>
    void make_expl(int var, int slack, E& ex) {
      assert(slack >= 0);
#if 0
      for(elt e : xs) {
        assert(s->state.is_inconsistent(e.x < e.x.lb()));
        ex.push(e.x < e.x.lb());
      }
      for(elt e : ys) {
        assert(s->state.is_inconsistent(e.x > e.x.ub()));
        ex.push(e.x > e.x.ub());
      }
#else
      vec<int> xs_pending;
      vec<int> ys_pending;
      // First, collect things we can omit entirely, or
      // include at the previous decision level
      for(int xi : irange(0, xs.size())) {
        if(2*xi == var)
          continue;
        elt e = xs[xi];

        int x_lb = e.x.lb();
#ifndef SKIP_L0
        int x_lb_0 = e.x.lb_0();
        int diff_0 = e.c * (x_lb - x_lb_0);
        if(diff_0 <= slack) {
          slack -= diff_0;
          continue;
        }
#endif
        int x_lb_p = e.x.lb_prev();
        int diff_p = e.c * (x_lb - x_lb_p);
        if(diff_p <= slack) {
          slack -= diff_p;
          ex.push(e.x < x_lb_p); 
          continue;
        }
        xs_pending.push(xi);
      }
      for(int yi : irange(0, ys.size())) {
        if(2*yi+1 == var)
          continue;
        elt e = ys[yi];
        int y_ub = e.x.ub();
#ifndef SKIP_L0
        int y_ub_0 = e.x.ub_0();
        int diff_0 = e.c * (y_ub_0 - y_ub);
        if(diff_0 <= slack) {
          slack -= diff_0;
          continue;
        }
#endif
        int y_ub_p = e.x.ub_prev();
        int diff_p = e.c * (y_ub_p - y_ub);
        if(diff_p <= slack) {
          slack -= diff_p;
          ex.push(e.x > y_ub_p);
          continue;
        }
        ys_pending.push(yi);
      }

      // Then, add things at the current level
      assert(slack >= 0);
      for(int xi : xs_pending) {
        elt e = xs[xi];
        int diff = slack/e.c;
        ex.push(e.x < e.x.lb() - diff);
        slack -= e.c * diff;
        assert(slack >= 0);
      }
      for(int yi : ys_pending) {
        elt e = ys[yi];
        int diff = slack/e.c;
        ex.push(e.x > e.x.ub() + diff);
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
        x_lb += e.c * e.x.lb();
      int y_ub = 0;
      for(elt e : ys)
        y_ub += e.c * e.x.ub();

      if(x_lb - y_ub  > k) {
        // Collect enough atoms to explain the sum.
        // FIXME: This is kinda weak. We really want to
        // push as much as we can onto the previous level.
        make_expl(Var_None, x_lb - y_ub - k - 1, confl);
        /* /
        for(elt e : xs)
          confl.push(e.x < e.x.lb());
        for(elt e : ys)
          confl.push(e.x > e.x.ub());
        / */

        // NOT_YET;
#ifdef CHECK_STATE
        assert(confl_is_current(s, confl));
#endif
        return false; 
      }

      // Otherwise, propagate upper bounds.
      int slack = k - x_lb + y_ub;
      for(int xi : irange(0, xs.size())) {
        elt e = xs[xi];
        int x_diff = slack/e.c;
        int x_ub = e.x.lb() + x_diff;
        if(x_ub < e.x.ub()) {
          // Build the explanation
          /*
          expl_builder ex(s->persist.alloc_expl(xs.size()+ys.size()));
          make_expl(2*xi, slack - e.c * x_diff, ex);
          if(!e.x.set_ub(x_ub, *ex))
          */
#ifdef EXPL_EAGER
          if(!e.x.set_ub(x_ub,
              expl_thunk { ex_eager, this, make_eager_expl(2*xi) }))
#else
          if(!e.x.set_ub(x_ub,
              expl_thunk { ex_x, this, xi, expl_thunk::Ex_BTPRED }))
//            if(!e.x.set_ub(x_ub,
//                ex_thunk(ex_nil<&P::ex_naive>, 2*xi, expl_thunk::Ex_BTPRED)))
#endif
            return false;
        }
      }

      for(int yi : irange(0, ys.size())) {
        elt e = ys[yi];
        // int y_diff = slack/e.c;
        int y_diff = slack/e.c;
        int y_lb = e.x.ub() - y_diff;
        if(e.x.lb() < y_lb) {
          /*
          expl_builder ex(s->persist.alloc_expl(xs.size()+ys.size()));
          make_expl(2*yi+1, slack - e.c * y_diff, ex);
          if(!e.x.set_lb(y_lb, *ex))
          */
#ifdef EXPL_EAGER
          if(!e.x.set_lb(y_lb,
              expl_thunk { ex_eager, this, make_eager_expl(2*yi + 1) }))
#else
          if(!e.x.set_lb(y_lb,
              expl_thunk { ex_y, this, yi, expl_thunk::Ex_BTPRED }))
//          if(!e.x.set_lb(y_lb,
//                ex_thunk(ex_nil<&P::ex_naive>, 2*yi+1, expl_thunk::Ex_BTPRED)))
#endif
            return false;
        }
      }
      return true;
    }

    vec<elt> xs;
    vec<elt> ys;
    int k;

#ifdef EXPL_EAGER
    // Eager explanations
    vec< vec<patom_t> > expls;
    unsigned int expls_sz;
#endif
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
      lb += e.c * e.x.lb();
    for(const elt& e : ys)
      lb -= e.c * e.x.ub();
    return lb;
  }

  watch_result wake_r(int xi) {
    trail_change(s->persist, status, (char) S_Active);

    // Compute the threshold
    int new_threshold = 0;
    for(const elt& e : xs)
      new_threshold = std::max(new_threshold, (int) (e.c * (e.x.ub() - e.x.lb())));
    for(const elt& e : ys)
      new_threshold = std::max(new_threshold, (int) (e.c * (e.x.ub() - e.x.lb())));
    if(slack < new_threshold) {
      queue_prop();
    } else {
      trail_change(s->persist, threshold, new_threshold);
    }
    return Wt_Keep;
  }

  watch_result wake_x(int xi) {
    if(status&S_Red)
      return Wt_Keep;

    trail_change(s->persist, slack, slack - delta(xs[xi].c, xs[xi].x.pid));
#ifdef CHECK_STATE
    // Might not have processed all watches yet
    assert(slack >= k - compute_lb());
#endif
    if(slack < threshold)
      queue_prop();
    return Wt_Keep;
  }

  watch_result wake_y(int yi) {
    if(status&S_Red)
      return Wt_Keep;
    trail_change(s->persist, slack, slack - delta(ys[yi].c, ys[yi].x.pid^1));
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
      if(2*xi == ei)
        continue;
      expl.push(xs[xi].x < xs[xi].x.lb());
    }
    for(int yi = 0; yi < ys.size(); yi++) {
      if(2*yi+1 == ei)
        continue;
      expl.push(ys[yi].x > ys[yi].x.ub());
    }
    /*
    for(elt e : p->xs)
      expl.push(e.x < e.x.lb());
    for(elt e : p->ys)
      expl.push(e.x > e.x.ub());
      */
  }

  void ex_r(int ex_slack, vec<clause_elt>& expl) {
    make_expl(Var_None, ex_slack, expl);
  }

  void ex_x(int xi, pval_t pval, vec<clause_elt>& expl) {
#ifndef EXPL_NAIVE
    intvar::val_t ival(to_int(pval_inv(pval)));
    intvar::val_t lim(k - xs[xi].c*(ival+1) + 1);

    intvar::val_t sum = 0;
    for(int xj : irange(xi))
      sum += xs[xj].c * xs[xj].x.lb();
    for(int xj : irange(xi+1, xs.size()))
      sum += xs[xj].c * xs[xj].x.lb();
    for(elt e : ys)
      sum -= e.c * e.x.ub();
    expl.push(~r);
    make_expl(2*xi, sum - lim, expl);
#else
    // Naive explanation
    expl.push(~r);
    for(elt e : xs) {
      assert(s->state.is_inconsistent(e.x < e.x.lb()));
      expl.push(e.x < e.x.lb());
    }
    for(elt e : ys) {
      assert(s->state.is_inconsistent(e.x > e.x.ub()));
      expl.push(e.x > e.x.ub());
    }
#endif
  }

  void ex_y(int yi, pval_t pval, vec<clause_elt>& expl) {
#ifndef EXPL_NAIVE
    intvar::val_t ival(to_int(pval));
    intvar::val_t lim(k + ys[yi].c*(ival-1) + 1);

    intvar::val_t sum = 0;
    for(elt e : xs)
      sum += e.c * e.x.lb();
    for(int yj : irange(yi))
      sum -= ys[yj].c * ys[yj].x.ub();
    for(int yj : irange(yi+1, ys.size()))
      sum -= ys[yj].c * ys[yj].x.ub();

    expl.push(~r);
    make_expl(2*yi+1, sum - lim, expl);
#else
    expl.push(~r);
    for(elt e : xs) {
      assert(s->state.is_inconsistent(e.x < e.x.lb()));
      expl.push(e.x < e.x.lb());
    }
    for(elt e : ys) {
      assert(s->state.is_inconsistent(e.x > e.x.ub()));
      expl.push(e.x > e.x.ub());
    }
#endif
  }

#ifdef EXPL_EAGER
  void ex_eager(int pi, pval_t pval,
                       vec<clause_elt>& expl) {
    lin_le_inc* p(static_cast<lin_le_inc*>(ptr));

    for(patom_t at : expls[pi])
      expl.push(at);
  }

  // Allocate a new reason (to be garbage collected)
  int make_eager_expl(int var) {
    trail_push(s->persist, expls_sz);
    int pi = expls_sz++;
    if(expls.size() < expls_sz)
      expls.push();
    vec<patom_t>& expl(expls[pi]);
    expl.clear();

    for(int ii = 0; ii < xs.size(); ii++) {
      if(ii != 2*var) {
        elt e = xs[ii];
        expl.push(e.x < e.x.lb());
      }
    }
    for(int ii = 0; ii < ys.size(); ii++) {
      if(ii != 2*var + 1) {
        elt e = ys[ii];
        expl.push(e.x > e.x.ub());
      }
    }
    
    return pi;
  }
#endif

  public: 

    lin_le_inc(solver_data* s, patom_t _r, vec<int>& ks, vec<intvar>& vs, int _k)
      : propagator(s), r(_r), k(_k), slack(k), threshold(0), status(0)
#ifdef EXPL_EAGER
        , expls_sz(0)
#endif 
      {
      for(int ii = 0; ii < vs.size(); ii++) {
        if(ks[ii] > 0) {
          // vs[ii].attach(E_LB, watch_callback(wake_x, this, xs.size(), true));
          vs[ii].attach(E_LB, watch<&P::wake_x>(xs.size(), Wt_IDEM));
          xs.push(elt(ks[ii], vs[ii]));
        } else if(ks[ii] < 0) {
          // vs[ii].attach(E_UB, watch_callback(wake_y, this, ys.size(), true));
          vs[ii].attach(E_UB, watch<&P::wake_y>(ys.size(), Wt_IDEM));
          ys.push(elt(-ks[ii], vs[ii]));
        }
      }
      // Initialize lower bound
      for(const elt& e : xs)
        slack -= e.c * e.x.lb_prev();
      for(const elt& e : ys)
        slack += e.c * e.x.ub_prev();
      // Tighten upper bound, and compute threshold? 
      if(s->state.is_entailed(r)) {
        status = S_Active;
        for(elt& e : xs) {
          int x_ub = e.x.lb() + slack/e.c;
          if(x_ub < e.x.ub())
            e.x.set_ub(x_ub, reason());
          threshold = std::max(threshold, (int) (e.c * (e.x.ub() - e.x.lb_prev())));
        }
        for(elt& e : ys) {
          int y_lb = e.x.ub() - slack/e.c;
          if(y_lb > e.x.lb())
            e.x.set_lb(y_lb, reason());
          threshold = std::max(threshold, (int) (e.c * (e.x.ub_prev() - e.x.lb())));
        }
        assert(slack >= k - compute_lb());
      } else {
        for(elt& e : xs) {
          int x_ub = e.x.lb() + slack/e.c;
          if(x_ub < e.x.ub())
            add_clause(s, ~r, e.x <= x_ub);
        }
        for(elt& e : ys) {
          int y_lb = e.x.ub() - slack/e.c;
          if(y_lb > e.x.lb())
            add_clause(s, ~r, e.x >= y_lb);
        }
        threshold = 0;
      }
    }

    void root_simplify(void) {
        
    }
    
    template<class E>
    void make_expl(int var, int slack, E& ex) {
      assert(slack >= 0);
      vec<int> xs_pending;
      vec<int> ys_pending;
      // First, collect things we can omit entirely, or
      // include at the previous decision level
      for(int xi : irange(0, xs.size())) {
        if(2*xi == var)
          continue;
        elt e = xs[xi];

        int x_lb = e.x.lb();
        int x_lb_0 = e.x.lb_0();
        int diff_0 = e.c * (x_lb - x_lb_0);
        if(diff_0 <= slack) {
          slack -= diff_0;
          continue;
        }
        xs_pending.push(xi);
      }

      for(int yi : irange(0, ys.size())) {
        if(2*yi+1 == var)
          continue;
        elt e = ys[yi];
        int y_ub = e.x.ub();
        int y_ub_0 = e.x.ub_0();
        int diff_0 = e.c * (y_ub_0 - y_ub);
        if(diff_0 <= slack) {
          slack -= diff_0;
          continue;
        }
        ys_pending.push(yi);
      }

      int* xp = xs_pending.begin();
      for(int xi : xs_pending) {
        elt e = xs[xi];
        int x_lb = e.x.lb();
        int x_lb_p = e.x.lb_prev();
        int diff_p = e.c * (x_lb - x_lb_p);
        if(diff_p <= slack) {
          slack -= diff_p;
          ex.push(e.x < x_lb_p); 
          continue;
        }
        *xp = xi; ++xp;
      }
      xs_pending.shrink_(xs_pending.end() - xp);

      int* yp = ys_pending.begin();
      for(int yi : ys_pending) {
        elt e = ys[yi];
        int y_ub = e.x.ub();
        int y_ub_p = e.x.ub_prev();
        int diff_p = e.c * (y_ub_p - y_ub);
        if(diff_p <= slack) {
          slack -= diff_p;
          ex.push(e.x > y_ub_p);
          continue;
        }
        *yp = yi; ++yp;
      }
      ys_pending.shrink_(ys_pending.end() - yp);

      // Then, add things at the current level
      assert(slack >= 0);
      for(int xi : xs_pending) {
        elt e = xs[xi];
        int diff = slack/e.c;
        ex.push(e.x < e.x.lb() - diff);
        slack -= e.c * diff;
        assert(slack >= 0);
      }
      for(int yi : ys_pending) {
        elt e = ys[yi];
        int diff = slack/e.c;
        ex.push(e.x > e.x.ub() + diff);
        slack -= e.c * diff;
        assert(slack >= 0);
      }
    }

    bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_PROP
      std::cout << "[[Running linear_le(inc)]]" << std::endl;
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
//        make_expl(Var_None, -slack - 1, confl);
        trail_change(s->persist, status, (char) S_Red);
        return true;
#ifdef CHECK_STATE
//        assert(confl_is_current(s, confl));
#endif
      }

      if(!(status&S_Active))
        return true;

      // Otherwise, propagate upper bounds.
//      int slack = k - lb;
      int new_threshold = 0;
      for(int xi : irange(0, xs.size())) {
        elt e = xs[xi];
        int x_diff = slack/e.c;
        int x_ub = e.x.lb() + x_diff;
        if(x_ub < e.x.ub()) {
          // Build the explanation
          if(!e.x.set_ub(x_ub,
              ex_thunk(ex<&P::ex_x>, xi, expl_thunk::Ex_BTPRED)))
            return false;
        }
        new_threshold = std::max(new_threshold, (int) (e.c * (e.x.ub() - e.x.lb())));
      }

      for(int yi : irange(0, ys.size())) {
        elt e = ys[yi];
        // int y_diff = slack/e.c;
        int y_diff = slack/e.c;
        int y_lb = e.x.ub() - y_diff;
        if(e.x.lb() < y_lb) {
          if(!e.x.set_lb(y_lb,
              ex_thunk(ex<&P::ex_y>, yi, expl_thunk::Ex_BTPRED)))
            return false;
        }
        new_threshold = std::max(new_threshold, (int) (e.c * (e.x.ub() - e.x.lb())));
      }
      trail_change(s->persist, threshold, new_threshold);
      return true;
    }

    patom_t r;
    vec<elt> xs;
    vec<elt> ys;
    int k;

    // Persistent state
    int slack;
    int threshold;
    char status;
};


// MDD-style decomposition.
// Introduce partial-sum variables, but coalesce ranges which
// are equivalent.
class linear_decomposer {
public:  
  linear_decomposer(solver_data* _s, vec<int>& _ks, vec<intvar>& _vs)
    : s(_s), ks(_ks), vs(_vs) { }

  void operator()(int k) {
    // Clear temporary state 
    tbl.clear();
    red_ubs.clear(); red_ubs.growTo(vs.size());
    feas_ubs.clear(); feas_ubs.growTo(vs.size());

    // Set up feasible ranges for partial sums
    int feas_ub = k;
    int red_ub = k;
    for(int r_ii : irange(1, vs.size()+1)) {
      int ii = vs.size() - r_ii;

      if(ks[ii] > 0) {
        red_ub -= ks[ii] * vs[ii].ub();
        feas_ub -= ks[ii] * vs[ii].lb();
      }
      if(ks[ii] < 0) {
        red_ub -= ks[ii] * vs[ii].lb();
        feas_ub -= ks[ii] * vs[ii].ub();
      }

      feas_ubs[ii] = feas_ub;
      red_ubs[ii] = red_ub;
    }
    
    if(red_ubs[0] < 0) {
      WARN("WARNING: Linear is satisfied by initial bounds.");
      return;
    }
    if(feas_ubs[0] < 0) {
      ERROR;
    }

    // Allocate partial sum predicates
    // Don't need first (since it's ks[0] * xs[0])
    // or last variable.
    /*
    for(int _ii : irange(vs.size()-2))
      ps_preds.push(new_pred(*s));
      */

    NOT_YET_WARN;
      
    decompose(0, k);
  }
protected:
  struct entry_t {
    entry_t(intvar::val_t _st, intvar::val_t _en, pval_t _val)
      : st(_st), en(_en), val(_val) { }

    intvar::val_t st, en;
    pval_t val;
  };

  int decompose(int idx, intvar::val_t lim) {
    assert(idx < vs.size()); 
     
    return 0;       
  }

  solver_data* s; 
  vec<int>& ks;
  vec<intvar>& vs;

  std::map<intvar::val_t, entry_t> tbl;
  // Upper bounds for feasibility and redundance
  vec<intvar::val_t> red_ubs;
  vec<intvar::val_t> feas_ubs;
  vec<pid_t> ps_preds;
};

class int_linear_ne : public propagator, public prop_inst<int_linear_ne> {
  enum { Var_None = 0 };
  enum { P_Deact = 1, P_Prop = 2};
  enum { S_Active = 1, S_Red = 2 };

  // See if we can find some other unfixed variable
  watch_result wake_bound(int vi) {
    if(!vs[perm[1]].x.is_fixed())
      return Wt_Drop;
    if(status&S_Active)
      queue_prop();
    return Wt_Keep;
  }

  watch_result wake_fix(int vi) {
    if(status&S_Red)
      return Wt_Keep;

    // Just like two-literal watching, find a replacement watch
    if(perm[1] != vi) {
      perm[0] = perm[1];
    }

    for(int pi = 2; pi < perm.size(); ++pi) {
      int wi = perm[pi];
      if(!vs[wi].x.is_fixed()) {
        perm[1] = wi;
        perm[pi] = vi;
        vs[wi].x.attach(E_FIX, watch<&P::wake_fix>(wi, Wt_IDEM));
        return Wt_Drop;
      }
    }
    // None found
    if(!vs[perm[0]].x.is_fixed()) {
      int x0 = perm[0];
      vs[x0].x.attach(E_LU, watch<&P::wake_bound>(x0, Wt_IDEM)); 
    }
    queue_prop();  
    return Wt_Keep;
  }

  watch_result wake_r(int vi) {
    if(vs[perm[1]].x.is_fixed())
      queue_prop();
    return Wt_Keep;   
  }

  void expl(int xi, vec<clause_elt>& expl) {
    if(xi != Var_None)
      expl.push(~r);
    for(int ii = 0; ii < xi; ii++) {
      assert(vs[ii].x.is_fixed());
      expl.push(vs[ii].x < vs[ii].x.lb());
      expl.push(vs[ii].x > vs[ii].x.ub());
    }
    int sz = vs.size();
    for(int ii = xi+1; ii < sz; ++ii) {
      // expl.push(vs[ii].x != vs[ii].x.lb());
      assert(vs[ii].x.is_fixed());
      expl.push(vs[ii].x < vs[ii].x.lb());
      expl.push(vs[ii].x > vs[ii].x.ub());
    }
  }

public:
  struct elt {
    elt(int _c, intvar _x)
      : c(_c), x(_x) { }
    int c;
    intvar x;
  };
  
  int_linear_ne(solver_data* s, patom_t _r, vec<int>& ks, vec<intvar>& xs, int _k)
    : propagator(s), r(_r), k(_k), status(0) {
    assert(xs.size() >= 2);
    for(int ii = 0; ii < xs.size(); ii++) {
      vs.push(elt { ks[ii], xs[ii] });
      perm.push(ii);
    }
    xs[0].attach(E_FIX, watch<&P::wake_fix>(0, Wt_IDEM));
    xs[1].attach(E_FIX, watch<&P::wake_fix>(1, Wt_IDEM));
  }

  bool propagate(vec<clause_elt>& confl) {
    // Find the first un-fixed variable   
#ifdef LOG_PROP
    std::cout << "[[Running linear_ne]]" << std::endl;
#endif
    elt* e = vs.begin();
    elt* end = vs.end();

    int r = k;
    for(; e != end; ++e) {
      elt el = *e;
      if(!el.x.is_fixed())
        goto found_unfixed;
      r -= el.c * el.x.lb();
    }
    // All fixed
    if(r == 0) {
      // Set the conflict.
      // Could use x < e.x.lb() \/ x > e.x.ub() instead.
      for(elt e : vs) {
        // confl.push(e.x != e.x.lb());    
        confl.push(e.x < e.x.lb());    
        confl.push(e.x > e.x.ub());    
      }
      return false; 
    }
    return true;

found_unfixed:
    elt* fst = e; 
    for(++e; e != end; ++e) {
      elt el = *e;
      if(!el.x.is_fixed()) {
        // Two unfixed variables.
        return true;
      }
      r -= el.c * el.x.lb();
    }
    
    int gap = r/fst->c;
//    if(r % fst->c == 0 && in_domain(fst->x, gap)) {
//      if(!enqueue(*s, fst->x != gap, expl_thunk { expl, this, (int) (fst - vs.begin()) }))
//        return false;
//    }
    if(r % fst->c == 0) {
      if(fst->x.lb() == gap) {
        if(!fst->x.set_lb(gap+1, ex_thunk(ex_nil<&P::expl>, (int) (fst - vs.begin()))))
          return false;
      } else if(fst->x.ub() == gap) {
        if(!fst->x.set_ub(gap-1, ex_thunk(ex_nil<&P::expl>, (int) (fst - vs.begin()))))
          return false;
      }
    }
    return true;
  }

  // virtual bool check_sat(void) { return true; }
  // void root_simplify(void) { }
  patom_t r;

  vec<elt> vs;
  int k;

  vec<int> perm;

  char status;
};

void linear_le_dec(solver_data* s, vec<int>& ks, vec<intvar>& vs, int k) {
  linear_decomposer dec(s, ks, vs);
  dec(k);
}

bool linear_le(solver_data* s, vec<int>& ks, vec<intvar>& vs, int k,
  patom_t r) {
  /*
  if(!s->state.is_entailed_l0(r)) {
    WARN("Half-reification not yet implemented for linear_le.");
  }
  */
//  new int_linear_le(s, r, ks, vs, k);
  new lin_le_inc(s, r, ks, vs, k);
  return true;
}

bool linear_ne(solver_data* s, vec<int>& ks, vec<intvar>& vs, int k,
  patom_t r) {
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
  return true;
}

}
