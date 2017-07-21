#include <utility>
#include <algorithm>
#include "engine/propagator.h"
#include "engine/propagator_ext.h"
#include "solver/solver_data.h"
#include "vars/intvar.h"

#include "utils/interval.h"
#include "mtl/p-sparse-set.h"

// #define DEBUG_ELEM

namespace phage {

typedef std::pair<int, int> ipair;

bool int_element(solver_data* s, patom_t r, intvar z, intvar x,
                   vec<int>& ys, int base) {
  // Also set domain of ys.
  if(s->state.is_entailed_l0(r)) {
    if(base > x.lb(s))
      enqueue(*s, x >= base, reason());
    if(base + ys.size() <= x.ub(s))
      enqueue(*s, x <= base + ys.size()-1, reason());
    // z.set_lb(ys_uniq[0], reason()); z.set_ub(ys_uniq.last(), reason());

    if(!make_sparse(z, ys))
      return false;
  } else {
    if(!add_clause(s, ~r, x >= base))
      return false;
    if(!add_clause(s, ~r, x < base + ys.size()))
      return false;

    vec<clause_elt> ps { ~r };
    for(int y : ys)
      ps.push(z == y);
    if(!add_clause(*s, ps))
      return false;
  }

  for(int ii : irange(ys.size())) {
    if(!add_clause(s, ~r, x != ii + base, z == ys[ii]))
      return false;
  }

  vec<int> ys_uniq(ys); uniq(ys_uniq);

  for(int yy : ys_uniq) {
    vec<clause_elt> ps { ~r, z != yy };
//    ps.push(z != yy);
    for(int ii : irange(ys.size())) {
      if(ys[ii] == yy) {
        ps.push(x == ii + base);
      }
    }
    if(!add_clause(*s, ps))
      return false;
  }

  return true;
}

class elem_var_bnd : public propagator, public prop_inst<elem_var_bnd> {
  // Wakeup and explanation
  static void ex_naive(elem_var_bnd* p, int yi, vec<clause_elt>& expl) {
    expl.push(p->x < p->x.lb(p->s));
    expl.push(p->x > p->x.ub(p->s));
    expl.push(p->z < p->z.lb(p->s));
    expl.push(p->z > p->z.ub(p->s));
    for(intvar& y : p->ys) {
      expl.push(y < y.lb(p->s));
      expl.push(y > y.ub(p->s));
    }
  }

  static void ex_y_lb(elem_var_bnd* p, int yi, intvar::val_t lb, vec<clause_elt>& expl) {
    // expl.push(p->x != yi + p->base);
    expl.push(p->x < yi + p->base);
    expl.push(p->x > yi + p->base);
    expl.push(p->z < lb);
  }

  static void ex_y_ub(elem_var_bnd* p, int yi, intvar::val_t ub, vec<clause_elt>& expl) {
    expl.push(p->x < yi + p->base);
    expl.push(p->x > yi + p->base);
    expl.push(p->z > ub);
  }
   
  void ex_x_lb(int vi, pval_t p, vec<clause_elt>& expl) {
    expl.push(x < vi+base);
    push_hints(vi, x.lb_of_pval(p) - base, expl);
  }

  void ex_x_ub(int vi, pval_t p, vec<clause_elt>& expl) {
    expl.push(x > vi+base);
    push_hints(x.ub_of_pval(p)-base+1, vi+1, expl);
  }

  /*
  static void ex_z(void* ptr, int pos, pval_t pval, vec<clause_elt>& expl) {
    NOT_YET;
  }
  */
  void ex_z_lb(int _vi, pval_t p, vec<clause_elt>& expl) {
    // fprintf(stderr, "elem_bnd::ex::lb(z)\n");
    intvar::val_t z_lb = z.lb_of_pval(p);

    expl.push(x < lb(x));
    expl.push(x > ub(x));

    intvar::val_t z_step = lb_0(z);
    for(int yi = lb(x) - base; yi <= ub(x) - base; yi++) {
      if(ub(ys[yi]) < z_lb)
        z_step = std::max(z_step, ub(ys[yi]));
      else
        expl.push(ys[yi] < z_lb);
    }
    if(z_step > lb_0(z))
      expl.push(z <= z_step);
  }

  void ex_z_ub(int _vi, pval_t p, vec<clause_elt>& expl) {
    // fprintf(stderr, "elem_bnd::ex::ub(z)\n");
    int z_ub = z.ub_of_pval(p); 

    expl.push(x < lb(x));
    expl.push(x > ub(x));

    intvar::val_t z_step = ub_0(z);
    for(int yi = lb(x) - base; yi <= ub(x) - base; yi++) {
      if(lb(ys[yi]) > z_ub)
        z_step = std::min(lb(ys[yi]), z_step);
      else
        expl.push(ys[yi] > z_ub);
    }
    if(z_step < ub_0(z))
      expl.push(z >= z_step);
  }

  void push_hints(int low, int high, vec<clause_elt>& expl) {
    intvar::val_t z_ub = z.ub(s);

    intvar::val_t z_low = lb_0(z);
    intvar::val_t z_high = ub_0(z)+1;

    for(int ii : irange(low, high)) {
      intvar::val_t hint = cut_hint[ii];
      if(z_ub < hint) {
        assert(ys[ii].lb(s) >= hint);
        z_high = std::min(z_high, hint);
        expl.push(ys[ii] < hint);
      } else {
        assert(z.lb(s) >= hint);
        expl.push(ys[ii] >= hint);
        z_low = std::max(z_low, hint);
      }
    }
    expl.push(z < z_low);
    expl.push(z >= z_high);
  }
public:
  elem_var_bnd(solver_data* _s, intvar _z, intvar _x, vec<intvar>& _ys, int _base, patom_t _r)
    : propagator(_s), base(_base), x(_x), z(_z), ys(_ys), r(_r) {
    x.attach(E_LU, watch_callback(wake_default, this, 0, true));
    z.attach(E_LU, watch_callback(wake_default, this, 0, true));
    for(int ii : irange(ys.size())) {
      ys[ii].attach(E_LU, watch_callback(wake_default, this, ii, true)); 
      cut_hint.push(ys[ii].lb(s));
    }
    // Set initial bounds
    if(base > x.lb(s))
      set_lb(x,base, reason());
    if(base + ys.size() < x.ub(s))
      set_ub(x,base + ys.size(), reason()); 
  }

  void root_simplify(void) {
    
  }
    
   bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running elem_var_bnd]]" << std::endl;
#endif
       
      int_itv z_dom { z.lb(s), z.ub(s) };
      int_itv z_supp { z.ub(s)+1, z.lb(s)-1 };

      // Run forward, to find the lower bound
      int vi = x.lb(s) - base;
      int vend = x.ub(s) + 1 - base;

      for(; vi != vend; ++vi) {
        int_itv y_dom { ys[vi].lb(s), ys[vi].ub(s) };
        int_itv y_supp = z_dom & y_dom;
        if(y_supp.empty()) {
          cut_hint[vi] = std::max(z_dom.lb, y_dom.lb);
        } else {
          z_supp = y_supp;
          break;
        }
      }
      int low = vi;

      if(low + base > x.lb(s)) {
        // if(!set_lb(x,low + base, ex_thunk(ex_nil<ex_naive>, vi, expl_thunk::Ex_BTPRED)))
        if(!set_lb(x,low + base, ex_thunk(ex<&P::ex_x_lb>, lb(x)-base, expl_thunk::Ex_BTPRED)))
          return false;
      }

      int high = vi;
      for(++vi; vi != vend; ++vi) {
        int_itv y_dom { ys[vi].lb(s), ys[vi].ub(s) };
        int_itv y_supp = z_dom & y_dom;
        if(y_supp.empty()) {
          cut_hint[vi] = std::max(z_dom.lb, y_dom.lb);
        } else {
          z_supp |= y_supp;
          high = vi;
        }
      }
      if(high + base < x.ub(s)) {
        // if(!set_ub(x,high + base, ex_thunk(ex_nil<ex_naive>, high, expl_thunk::Ex_BTPRED)))
        if(!set_ub(x,high + base, ex_thunk(ex<&P::ex_x_ub>, ub(x) - base, expl_thunk::Ex_BTPRED)))
          return false;
      }

      if(z_supp.lb > z.lb(s)) {
        // if(!set_lb(z, z_supp.lb, ex_thunk(ex_nil<ex_naive>, 0, expl_thunk::Ex_BTPRED)))
        if(!set_lb(z, z_supp.lb, ex_thunk(ex<&P::ex_z_lb>, 0, expl_thunk::Ex_BTPRED)))
          return false;
      }
      if(z_supp.ub < z.ub(s)) {
        // if(!set_ub(z, z_supp.ub, ex_thunk(ex_nil<ex_naive>, 0, expl_thunk::Ex_BTPRED)))
        if(!set_ub(z, z_supp.ub, ex_thunk(ex<&P::ex_z_ub>, 0, expl_thunk::Ex_BTPRED)))
          return false;
      }

      if(low == high) {
        intvar& y = ys[low];
        if(z_supp.lb > y.lb(s)) {
          // if(!y.set_lb(z_supp.lb, ex_thunk(ex_nil<ex_naive>, 0, expl_thunk::Ex_BTPRED)))
          if(!set_lb(y, z_supp.lb, ex_thunk(ex_lb<ex_y_lb>, low)))
            return false;
        }
        if(z_supp.ub < y.ub(s)) {
          // if(!y.set_ub(z_supp.ub, ex_thunk(ex_nil<ex_naive>, 0, expl_thunk::Ex_BTPRED)))
          if(!set_ub(y, z_supp.ub, ex_thunk(ex_ub<ex_y_ub>, low)))
           return false;
        }
      }

      return true;
    }

    int base;
    intvar x;
    intvar z;
    vec<intvar> ys;

    patom_t r;

    vec<intvar::val_t> cut_hint;
};

// Mixed propagator: domain consistent for x, but bounds-consistent for
// y and z.
class elem_var_mix : public propagator, public prop_inst<elem_var_mix> {
  // Wakeup and explanation
  enum Change { LB_SUPP = 1, UB_SUPP = 2, Z_LB = 4, Z_UB = 8 };
  enum Mode { E_Free, E_Fix };

  void kill_yi(int yi) {
    if(!live_yi.elem(yi))
      return;

    trail_push(s->persist, live_yi.sz);
    live_yi.remove(yi);

    if(z_lb_supp == yi) {
      change |= LB_SUPP;
      queue_prop();
    }
    if(z_ub_supp == yi) {
      change |= UB_SUPP;
      queue_prop();
    }
    if(live_yi.size() == 1) {
      trail_change(s->persist, mode, (unsigned char) E_Fix);
      queue_prop();
    }
  }

  watch_result wake_z(int evt) {
    change |= evt;
    queue_prop();
    return Wt_Keep;
  }
  watch_result wake_xi(int xi) {
    kill_yi(xi);
    return Wt_Keep;
  }

  watch_result wake_y_lb(int yi) {
    if(!live_yi.elem(yi))
      return Wt_Keep;

    if(lb(ys[yi]) > ub(z)) {
      supp[yi] = lb(ys[yi]);
      dead_yi.push(yi);
      queue_prop();
    } else if (z_lb_supp == yi && lb(ys[yi]) > lb(z)) {
      change |= LB_SUPP;
      queue_prop();
    }
    return Wt_Keep;
  }

  watch_result wake_y_ub(int yi) {
    assert(yi < live_yi.dom);
    assert(yi < ys.size());
    if(!live_yi.elem(yi))
      return Wt_Keep;

    if(ub(ys[yi]) < lb(z)) {
      supp[yi] = ub(ys[yi]);
      dead_yi.push(yi);
      queue_prop();
    } else if(z_ub_supp == yi && ub(ys[yi]) < ub(z)) {
      change |= UB_SUPP;
      queue_prop();
    }
    return Wt_Keep;
  }

  void cleanup(void) {
    change = 0;
    dead_yi.clear();
    is_queued = false;
  }

  void ex_y_lb(int yi, pval_t p, vec<clause_elt>& expl) {
    expl.push(x != yi + base);
    expl.push(z < ys[yi].lb_of_pval(p));
  }

  void ex_y_ub(int yi, pval_t p, vec<clause_elt>& expl) {
    expl.push(x != yi+base);
    expl.push(z > ys[yi].ub_of_pval(p));
  }
   
  void ex_x(int yi, pval_t _p, vec<clause_elt>& expl) {
    if(ub(z) < supp[yi]) {
      expl.push(ys[yi] < supp[yi]);
      expl.push(z >= supp[yi]);
    } else {
      assert(supp[yi] < lb(z));
      assert(ub(ys[yi]) < lb(z));
      expl.push(ys[yi] > supp[yi]);
      expl.push(z <= supp[yi]);
    }
  }

  void ex_z_lb(int live_end, pval_t p, vec<clause_elt>& expl) {
    intvar::val_t z_lb = z.lb_of_pval(p);

    for(int ii : irange(live_end)) {
      int yi = live_yi[ii];
      expl.push(ys[yi] < z_lb);
    }

    if(live_end == 1) {
      expl.push(x != live_yi[0] + base);
    } else {
      for(int ii : irange(live_end, ys.size())) {
        int yi = live_yi[ii];
        expl.push(x == yi + base);
      }
    }
  }

  void ex_z_ub(int live_end, pval_t p, vec<clause_elt>& expl) {
    intvar::val_t z_ub = z.ub_of_pval(p);

    for(int ii : irange(live_end)) {
      int yi = live_yi[ii];
      expl.push(ys[yi] > z_ub);
    }

    if(live_end == 1) {
      expl.push(x != live_yi[0] + base);
    } else {
      for(int ii : irange(live_end, ys.size())) {
        int yi = live_yi[ii];
        expl.push(x == yi + base);
      }
    }
  }

public:
  elem_var_mix(solver_data* _s, intvar _z, intvar _x, vec<intvar>& _ys, int _base, patom_t _r)
    : propagator(_s), base(_base), x(_x), z(_z), ys(_ys), r(_r),
      mode(E_Free), live_yi(ys.size()), supp(ys.size(), 0),
      z_lb_supp(0), z_ub_supp(0), change(0) {
    // Set all y-values as feasible
    live_yi.sz = ys.size();

    if(lb(x) < base)
      set_lb(x, base, reason());
    if(ub(x) > ys.size() + base)
      set_ub(x, ys.size()+base, reason());
    // Make sure all [x = k]s are available.
    make_eager(x);
    z.attach(E_LB, watch<&P::wake_z>(Z_LB, Wt_IDEM));
    z.attach(E_UB, watch<&P::wake_z>(Z_UB, Wt_IDEM));

    intvar::val_t z_lb = lb(z);
    intvar::val_t z_ub = ub(z);
    
    intvar::val_t yi_min = INT_MAX;
    intvar::val_t yi_max = INT_MIN;
    int low_yi = ys.size();
    int high_yi = ys.size();

    for(int yi : irange(lb(x) - base)) {
      live_yi.remove(yi);
    }
    for(int yi : irange(ub(x) - base + 1, ys.size())) {
      live_yi.remove(yi);
    }

    // Figure out bounds on the consistent y-values.
    for(int yi : live_yi) {
      int lb_yi = lb(ys[yi]);
      int ub_yi = ub(ys[yi]);
      if(lb_yi <= z_ub && z_lb <= ub_yi) {
        if(lb_yi < yi_min) {
          low_yi = yi;
          yi_min = lb_yi;
        }
        if(ub_yi > yi_max) {
          high_yi = yi;
          yi_max = ub_yi;
        }
      }
    }

    if(z_lb < low_yi) {
      set_lb(z, low_yi, reason());
    }
    z_lb_supp.x = low_yi;

    if(high_yi < z_ub) {
      set_ub(z, high_yi, reason());
    }
    z_ub_supp.x = high_yi;

    for(int yi : irange(lb(x)-base, ub(x)-base+1)) {
      assert(yi < ys.size());
      if(s->state.is_inconsistent(x == yi+base)) {
        assert(live_yi.elem(yi));
        live_yi.remove(yi);
        continue;
      }
      if(ub(ys[yi]) < z_lb || z_ub < lb(ys[yi])) {
        assert(live_yi.elem(yi));
        enqueue(*s, x != yi+base, reason());
        live_yi.remove(yi);
        continue;
      }

      attach(s, x != yi+base, watch<&P::wake_xi>(yi, Wt_IDEM));
      ys[yi].attach(E_LB, watch<&P::wake_y_lb>(yi, Wt_IDEM));
      ys[yi].attach(E_UB, watch<&P::wake_y_ub>(yi, Wt_IDEM));
      supp[yi] = std::max(lb(z), lb(ys[yi]));
    }
    // Set initial bounds
  }

  void root_simplify(void) {
    
  }
    
   void check_supps(void) {
     assert(!s->state.is_inconsistent(x == z_lb_supp + base));
     assert(!s->state.is_inconsistent(x == z_ub_supp + base));

     assert(lb(ys[z_lb_supp]) <= lb(z) && lb(z) <= ub(ys[z_lb_supp]));
     assert(ub(z) <= ub(ys[z_ub_supp]) && lb(ys[z_lb_supp]) <= ub(z));
   }

   void check_live(void) {
     for(int yi : live_yi) {
       assert(!s->state.is_inconsistent(x == yi + base));
       assert(lb(z) <= ub(ys[yi]) && lb(ys[yi]) <= ub(z));
     }

     for(int ii : irange(live_yi.size(), ys.size())) {
       assert(s->state.is_inconsistent(x == live_yi[ii] + base));
     }
   }

   bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running elem_var_mix]]" << std::endl;
#endif
////      static int count = 0;
//      fprintf(stderr, "elem_var_mix: #%d\n", ++count);

      // Deal with the dead ys.
      if(dead_yi.size() > 0) {
        trail_push(s->persist, live_yi.sz);
        for(int yi : dead_yi) {
          // assert(live_yi.elem(yi));
          // May have been killed again (in the meantime)
          // by posting x != yi+base.
          if(!live_yi.elem(yi))
            continue;

          if(!enqueue(*s, x != yi + base, ex_thunk(ex<&P::ex_x>, yi, expl_thunk::Ex_BTPRED)))
            return false;
          live_yi.remove(yi);

          if(yi == z_lb_supp)
            change |= LB_SUPP;
          if(yi == z_ub_supp)
            change |= UB_SUPP;
        }
        dead_yi.clear();

        if(live_yi.size() == 1) {
          trail_change(s->persist, mode, (unsigned char) E_Fix);
        }
        // Defer the failure to unit propagation.
        if(live_yi.size() == 0)
          return true;
      }
      assert(live_yi.size() > 0);

      // x is fixed: z = ys[x].           
      if(mode == E_Fix) {
        assert(live_yi.size() == 1);
        int yi = live_yi[0];
        if(lb(z) != lb(ys[yi])) {
          if(lb(z) < lb(ys[yi])) {
            if(!set_lb(z, lb(ys[yi]), ex_thunk(ex<&P::ex_z_lb>,1)))
              return false;
          } else {
            if(!set_lb(ys[yi], lb(z), ex_thunk(ex<&P::ex_y_lb>,yi)))
              return false;
          }
        }
        if(ub(z) != ub(ys[yi])) {
          if(ub(z) > ub(ys[yi])) {
            if(!set_ub(z, ub(ys[yi]), ex_thunk(ex<&P::ex_z_ub>,1)))
              return false;
          } else {
            if(!set_ub(ys[yi], ub(z), ex_thunk(ex<&P::ex_y_ub>, yi)))
              return false;
          }
        }
        return true;
      }

      // Otherwise, deal with LB/UB supports
      int live_sz = live_yi.size();
      bool saved = false;
      if(change&(Z_LB|Z_UB)) {
        // Removal invalidates iterators and swaps elements;
        // iterating backwards is safe.
        // FIXME: Correct way of doing this is using a min-max heap
        // tracking the support value. Then we only need to look at
        // vars where support is violated.
        if(change&Z_LB) {
          int z_lb = lb(z);
          for(int ii = live_yi.size()-1; ii >= 0; --ii) {
            int yi = live_yi[ii];
            if(ub(ys[yi]) < z_lb) {
              supp[yi] = ub(ys[yi]);
              if(!enqueue(*s, x != yi+base, ex_thunk(ex<&P::ex_x>,yi, expl_thunk::Ex_BTPRED)))
                return false;
              if(!saved) {
                trail_push(s->persist, live_yi.sz);
                saved = true;
              }
              live_yi.remove(yi);
            }
          }
        }
        if(change&Z_UB) {
          int z_ub = ub(z);
          for(int ii = live_yi.size()-1; ii >= 0; --ii) {
            int yi = live_yi[ii];
            if(z_ub < lb(ys[yi])) {
              supp[yi] = lb(ys[yi]);
              if(!enqueue(*s, x != yi+base, ex_thunk(ex<&P::ex_x>,yi, expl_thunk::Ex_BTPRED)))
                return false;
              if(!saved) {
                trail_push(s->persist, live_yi.sz);
                saved = true;
              }
              live_yi.remove(yi);
            }
          }
        }
        if(!live_yi.elem(z_lb_supp))
          change |= LB_SUPP;
        if(!live_yi.elem(z_ub_supp))
          change |= UB_SUPP;
      } /* else { */
        if(change&LB_SUPP) {
          int z_lb = lb(z);
          int lb_yi = ys.size();
          int lb_val = INT_MAX;
          for(int yi : live_yi) {
            assert(!s->state.is_inconsistent(x == yi + base));
            int y_lb = lb(ys[yi]);
            if(y_lb <= z_lb) {
              z_lb_supp.set(s->persist, yi);
              goto z_lb_found;
            } else if(y_lb < lb_val) {
              lb_yi = yi;
              lb_val = y_lb;
            }
          }
          if(!set_lb(z, lb_val, ex_thunk(ex<&P::ex_z_lb>,live_sz)))
            return false;
          z_lb_supp.set(s->persist, lb_yi);
        }
     z_lb_found:
        if(change&UB_SUPP) {
          int z_ub = ub(z);
          int ub_yi = ys.size();
          int ub_val = INT_MIN;
          for(int yi : live_yi) {
            int y_ub = ub(ys[yi]); 
            if(y_ub >= z_ub) {
              z_ub_supp.set(s->persist, yi);
              goto z_ub_found;
            } else if(y_ub > ub_val) {
              ub_yi = yi;
              ub_val = y_ub;
            }
          }
          if(!set_ub(z, ub_val, ex_thunk(ex<&P::ex_z_ub>,live_sz)))
            return false;
          z_ub_supp.set(s->persist, ub_yi);
        }
      /* } */
     z_ub_found:
#ifdef DEBUG_ELEM
      check_supps();
      check_live();
#endif
      change = 0;

      return true;
    }

    int base;
    intvar x;
    intvar z;
    vec<intvar> ys;

    patom_t r;

    // Is x fixed?
    unsigned char mode;

    p_sparseset live_yi;

    vec<intvar::val_t> supp; // What value shows z & ys[yi] != nil.
    Tint z_lb_supp; // Which yi supports lb(z)
    Tint z_ub_supp; // Which yi supports ub(z)

    vec<int> dead_yi;
    unsigned char change;
};


// Non-incremental interval-based propagation
class elem_var_simple : public propagator, public prop_inst<elem_var_simple> {
  // Wakeup and explanation
  static watch_result wake(void* ptr, int xi) {
    elem_var_simple* p(static_cast<elem_var_simple*>(ptr)); 
    p->queue_prop();
    return Wt_Keep;
  }

  // dom(z) inter dom(ys[i]) -> x != i.
  static void ex_x_ne_xi(void* ptr, int xi, pval_t pval, vec<clause_elt>& expl) {
    elem_var_simple* p(static_cast<elem_var_simple*>(ptr));
    
    intvar::val_t hint = p->cut_hint[xi];
    if(p->z.ub(p->s) < hint) {
      expl.push(p->z >= hint);
      expl.push(p->ys[xi] < hint);
    } else {
      expl.push(p->ys[xi] >= hint);
      expl.push(p->z < hint);
    }
  }

  static void ex_y_lb(elem_var_simple* p, int yi, intvar::val_t lb, vec<clause_elt>& expl) {
    expl.push(p->x != yi + p->base);
    expl.push(p->z < lb);
  }

  static void ex_y_ub(elem_var_simple* p, int yi, intvar::val_t ub, vec<clause_elt>& expl) {
    expl.push(p->x != yi + p->base);
    expl.push(p->z > ub);
  }

  static void ex_z_lb(P* p, int pos, intvar::val_t lb, vec<clause_elt>& expl) {
    NOT_YET;
  }

  static void ex_z_ub(P* p, int pos, intvar::val_t lb, vec<clause_elt>& expl) {
    NOT_YET;
  }

public:
  elem_var_simple(solver_data* _s, intvar _z, intvar _x, vec<intvar>& _ys, int _base, patom_t _r)
    : propagator(_s), base(_base), x(_x), z(_z), ys(_ys), r(_r) {
    // We assume the propagator is not half reified
    if(r != at_True) {
      NOT_YET;
    }
     
    // Set initial explanation hints
    for(intvar& y : ys)
      cut_hint.push(y.lb(s));
  }

  void root_simplify(void) {
    
  }
    
   // FIXME
   /*
   forceinline indom(intvar& x, int k) {
     if(DOM) {
       return x.man->in_domain(x.idx, k);
     } else {
       return x.lb(s) <= k && k <= x.ub(s);
     }
   }
   */

   bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running elem_var_simple]]" << std::endl;
#endif
       
      int_itv z_dom { z.lb(s), z.ub(s) };
      int_itv z_supp { z.ub(s)+1, z.lb(s)-1 };

      // Run forward, collect supported tuples
      intvar* y = ys.begin();
      intvar* end = ys.end();
      int vv = base;

      for(; y != end; ++y, ++vv) {
        if(!in_domain(s, x, vv))
          continue;

        int_itv y_supp = z_dom & int_itv {(*y).lb(s), (*y).ub(s)};
        if(y_supp.empty()) {
          if(!enqueue(*s, x != vv, expl_thunk { ex_x_ne_xi, this, vv - base }))
            return false;
        } else {
          z_supp = y_supp;
          goto support_found;
        }
      }

      // No support, definitely false.
      // But should have failed earlier
      ERROR;
      return false;

support_found:
      intvar* supp = y;
      for(++y, ++vv; y != end; ++y, ++vv) {
        int_itv y_supp = z_dom & int_itv {(*y).lb(s), (*y).ub(s)};
        if(y_supp.empty()) {
          if(!enqueue(*s, x != vv, expl_thunk { ex_x_ne_xi, this, vv - base }))
            return false;
        } else {
          z_supp |= y_supp;
          supp = end;
        }
      }

      if(z_supp.lb > z.lb(s)) {
        if(!set_lb(z, z_supp.lb, expl_thunk { ex_lb<ex_z_lb>, this, 0 }))
          return false;
      }

      if(z_supp.ub < z.ub(s)) {
        if(!set_ub(z, z_supp.ub, expl_thunk { ex_ub<ex_z_ub>, this, 1}))
          return false;
      }
       
      if(supp < end) {
        if(z_supp.lb > supp->lb(s)) {
          if(!set_lb(*supp, z_supp.lb, expl_thunk { ex_lb<ex_y_lb>, this, (int) (supp - ys.begin()), expl_thunk::Ex_BTPRED }))
            return false;
        }
        if(z_supp.ub < supp->ub(s)) {
          if(!set_ub(*supp, z_supp.ub, expl_thunk { ex_ub<ex_y_ub>, this, (int) (supp - ys.begin()), expl_thunk::Ex_BTPRED }))
            return false;
        }
      }
      return true;
    }

    // Constraint parameters
    int base;
    intvar x;
    intvar z;
    vec<intvar> ys;

    patom_t r;

    // Explanation hints
    vec<intvar::val_t> cut_hint;
};

bool int_element(solver_data* s, intvar x, intvar z, vec<int>& ys, patom_t r) {
  return int_element(s, r, x, z, ys, 1);
}

bool var_int_element(solver_data* s, intvar z, intvar x, vec<intvar>& ys, patom_t r) {
  // new elem_var_simple(s, x, i, ys, 1, r);
  new elem_var_bnd(s, z, x, ys, 1, r);
  // new elem_var_mix(s, z, x, ys, 1, r);
  return true; 
}
}
