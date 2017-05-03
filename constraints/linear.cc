#include <cassert>
#include <map>
#include "mtl/Vec.h"
#include "solver/solver_data.h"
#include "vars/intvar.h"

#include "engine/propagator_ext.h"

#define SKIP_L0
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
      if(ii != var) {
        elt e = xs[ii];
        expl.push(e.x < e.x.lb(s));
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
#ifdef EXPL_EAGER
          if(!set_ub(e.x, x_ub,
              expl_thunk { ex_eager, this, make_eager_expl(xi) }))
#else
          if(!set_ub(e.x, x_ub,
              expl_thunk { ex_x, this, xi, expl_thunk::Ex_BTPRED }))
//            if(!e.x.set_ub(x_ub,
//                ex_thunk(ex_nil<&P::ex_naive>, 2*xi, expl_thunk::Ex_BTPRED)))
#endif
            return false;
        }
      }

      return true;
    }

    vec<elt> xs;
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
      if(ii != var) {
        elt e = xs[ii];
        expl.push(e.x < e.x.lb(s));
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
        red_ub -= ks[ii] * vs[ii].ub(s);
        feas_ub -= ks[ii] * vs[ii].lb(s);
      }
      if(ks[ii] < 0) {
        red_ub -= ks[ii] * vs[ii].lb(s);
        feas_ub -= ks[ii] * vs[ii].ub(s);
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
    : propagator(s), r(_r), k(_k), status(0) {
    assert(xs.size() >= 2);
    for(unsigned int ii = 0; ii < xs.size(); ii++) {
      // FIXME
      make_eager(xs[ii]);
      vs.push(elt { ks[ii], xs[ii] });
      trigs.push(trigger { T_Var, ii });
    }
    if(!s->state.is_entailed(r)) {
      trigs.push(trigs[0]);
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
//   new int_linear_le(s, r, ks, vs, k);
  new lin_le_inc(s, r, ks, vs, k);
  return true;
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
  new int_linear_ne(s, r, ks, vs, k);
  return true;
}

}
