#include <utility>
#include <algorithm>
#include "engine/propagator.h"
#include "engine/propagator_ext.h"
#include "solver/solver_data.h"
#include "vars/intvar.h"

#include "utils/interval.h"

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
    push_hints(0, vi, expl);
  }

  void ex_x_ub(int vi, pval_t _p, vec<clause_elt>& expl) {
    push_hints(vi+1, ys.size(), expl);
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

    intvar::val_t z_low = ub_0(z)+1;
    intvar::val_t z_high = lb_0(z)-1;

    for(int ii : irange(low, high)) {
      intvar::val_t hint = cut_hint[ii];
      if(z_ub < hint) {
        assert(ys[ii].lb(s) >= hint);
        z_high = std::max(z_high, hint);
        expl.push(ys[ii] < hint);
      } else {
        assert(z.lb(s) >= hint);
        expl.push(ys[ii] >= hint);
        z_low = std::min(z_low, hint);
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
        if(!set_lb(x,low + base, ex_thunk(ex_nil<ex_naive>, vi, expl_thunk::Ex_BTPRED)))
        // if(!set_lb(x,low + base, ex_thunk(ex<&P::ex_x_lb>, vi, expl_thunk::Ex_BTPRED)))
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
        if(!set_ub(x,high + base, ex_thunk(ex_nil<ex_naive>, high, expl_thunk::Ex_BTPRED)))
        // if(!set_ub(x,high + base, ex_thunk(ex<&P::ex_x_ub>, high, expl_thunk::Ex_BTPRED)))
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
  return true; 
}
}
