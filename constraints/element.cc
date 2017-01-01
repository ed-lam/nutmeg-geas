#include <utility>
#include <algorithm>
#include "engine/propagator.h"
#include "solver/solver_data.h"
#include "vars/intvar.h"

#include "utils/interval.h"

namespace phage {

typedef std::pair<int, int> ipair;

bool int_element(solver_data* s, patom_t r, intvar z, intvar x,
                   vec<int>& ys, int base) {
  // Also set domain of ys.
  if(s->state.is_entailed_l0(r)) {
    x.set_lb(base, reason()); x.set_ub(base + ys.size()-1, reason());  
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
    vec<clause_elt> ps { ~r };
    ps.push(z != yy);
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
    expl.push(p->x < p->x.lb());
    expl.push(p->x > p->x.ub());
    expl.push(p->z < p->z.lb());
    expl.push(p->z > p->z.ub());
    for(intvar& y : p->ys) {
      expl.push(y < y.lb());
      expl.push(y > y.ub());
    }
  }

  static void ex_y_lb(elem_var_bnd* p, int yi, int64_t lb, vec<clause_elt>& expl) {
    // expl.push(p->x != yi + p->base);
    expl.push(p->x < yi + p->base);
    expl.push(p->x > yi + p->base);
    expl.push(p->z < lb);
  }

  static void ex_y_ub(elem_var_bnd* p, int yi, int64_t ub, vec<clause_elt>& expl) {
    expl.push(p->x < yi + p->base);
    expl.push(p->x > yi + p->base);
    expl.push(p->z > ub);
  }
   
  static void ex_x_lb(elem_var_bnd* p, int vi, vec<clause_elt>& expl) {
    p->push_hints(0, vi, expl);
  }

  static void ex_x_ub(elem_var_bnd* p, int vi, vec<clause_elt>& expl) {
    p->push_hints(vi+1, p->ys.size(), expl);
  }

  static void ex_z(void* ptr, int pos, pval_t pval, vec<clause_elt>& expl) {
    NOT_YET;
  }

  void push_hints(int low, int high, vec<clause_elt>& expl) {
    int64_t z_ub = z.ub();

    int64_t z_low = z.ub_0()+1;
    int64_t z_high = z.lb_0()-1;

    for(int ii : irange(low, high)) {
      int64_t hint = cut_hint[ii];
      if(z_ub < hint) {
        assert(ys[ii].lb() >= hint);
        z_high = std::max(z_high, hint);
        expl.push(ys[ii] < hint);
      } else {
        assert(z.lb() >= hint);
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
      cut_hint.push(ys[ii].lb());
    }
    // Set initial bounds
    if(base > x.lb())
      x.set_lb(base, reason());
    if(base + ys.size() < x.ub())
      x.set_ub(base + ys.size(), reason()); 
  }

  void root_simplify(void) {
    
  }
    
   bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running elem_var_bnd]]" << std::endl;
#endif
       
      int_itv z_dom { z.lb(), z.ub() };
      int_itv z_supp { z.ub()+1, z.lb()-1 };

      // Run forward, to find the lower bound
      int vi = x.lb() - base;
      int vend = x.ub() + 1 - base;

      for(; vi != vend; ++vi) {
        int_itv y_dom { ys[vi].lb(), ys[vi].ub() };
        int_itv y_supp = z_dom & y_dom;
        if(y_supp.empty()) {
          cut_hint[vi] = std::max(z_dom.lb, y_dom.lb);
        } else {
          z_supp = y_supp;
          break;
        }
      }
      int low = vi;

      if(low + base > x.lb()) {
        // if(!x.set_lb(low + base, ex_thunk(ex_nil<ex_x_lb>, vi)))
        if(!x.set_lb(low + base, ex_thunk(ex_nil<ex_naive>, vi, expl_thunk::Ex_BTPRED)))
          return false;
      }

      int high = vi;
      for(++vi; vi != vend; ++vi) {
        int_itv y_dom { ys[vi].lb(), ys[vi].ub() };
        int_itv y_supp = z_dom & y_dom;
        if(y_supp.empty()) {
          cut_hint[vi] = std::max(z_dom.lb, y_dom.lb);
        } else {
          z_supp |= y_supp;
          high = vi;
        }
      }
      if(high + base < x.ub()) {
        // if(!x.set_ub(high + base, ex_thunk(ex_nil<ex_x_ub>, high)))
        if(!x.set_ub(high + base, ex_thunk(ex_nil<ex_naive>, high, expl_thunk::Ex_BTPRED)))
          return false;
      }

      if(z_supp.lb > z.lb()) {
        if(!z.set_lb(z_supp.lb, ex_thunk(ex_nil<ex_naive>, 0, expl_thunk::Ex_BTPRED)))
          return false;
      }
      if(z_supp.ub < z.ub()) {
        if(!z.set_ub(z_supp.ub, ex_thunk(ex_nil<ex_naive>, 0, expl_thunk::Ex_BTPRED)))
          return false;
      }

      if(low == high) {
        intvar& y = ys[low];
        if(z_supp.lb > y.lb()) {
          // if(!y.set_lb(z_supp.lb, ex_thunk(ex_nil<ex_naive>, 0, expl_thunk::Ex_BTPRED)))
          if(!y.set_lb(z_supp.lb, ex_thunk(ex_lb<ex_y_lb>, low)))
            return false;
        }
        if(z_supp.ub < y.ub()) {
          // if(!y.set_ub(z_supp.ub, ex_thunk(ex_nil<ex_naive>, 0, expl_thunk::Ex_BTPRED)))
          if(!y.set_ub(z_supp.ub, ex_thunk(ex_ub<ex_y_ub>, low)))
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

    vec<int64_t> cut_hint;
};

// Non-incremental interval-based propagation
class elem_var_simple : public propagator, public prop_inst<elem_var_simple> {
  // Wakeup and explanation
  static void wake(void* ptr, int xi) {
    elem_var_simple* p(static_cast<elem_var_simple*>(ptr)); 
    p->queue_prop();
  }

  // dom(z) inter dom(ys[i]) -> x != i.
  static void ex_x_ne_xi(void* ptr, int xi, pval_t pval, vec<clause_elt>& expl) {
    elem_var_simple* p(static_cast<elem_var_simple*>(ptr));
    
    int64_t hint = p->cut_hint[xi];
    if(p->z.ub() < hint) {
      expl.push(p->z >= hint);
      expl.push(p->ys[xi] < hint);
    } else {
      expl.push(p->ys[xi] >= hint);
      expl.push(p->z < hint);
    }
  }

  static void ex_y_lb(elem_var_simple* p, int yi, int64_t lb, vec<clause_elt>& expl) {
    expl.push(p->x != yi + p->base);
    expl.push(p->z < lb);
  }

  static void ex_y_ub(elem_var_simple* p, int yi, int64_t ub, vec<clause_elt>& expl) {
    expl.push(p->x != yi + p->base);
    expl.push(p->z > ub);
  }

  static void ex_z_lb(P* p, int pos, int64_t lb, vec<clause_elt>& expl) {
    NOT_YET;
  }

  static void ex_z_ub(P* p, int pos, int64_t lb, vec<clause_elt>& expl) {
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
      cut_hint.push(y.lb());
  }

  void root_simplify(void) {
    
  }
    
   // FIXME
   /*
   forceinline indom(intvar& x, int k) {
     if(DOM) {
       return x.man->in_domain(x.idx, k);
     } else {
       return x.lb() <= k && k <= x.ub();
     }
   }
   */

   bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running elem_var_simple]]" << std::endl;
#endif
       
      int_itv z_dom { z.lb(), z.ub() };
      int_itv z_supp { z.ub()+1, z.lb()-1 };

      // Run forward, collect supported tuples
      intvar* y = ys.begin();
      intvar* end = ys.end();
      int vv = base;

      for(; y != end; ++y, ++vv) {
        if(!in_domain(x, vv))
          continue;

        int_itv y_supp = z_dom & int_itv {(*y).lb(), (*y).ub()};
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
        int_itv y_supp = z_dom & int_itv {(*y).lb(), (*y).ub()};
        if(y_supp.empty()) {
          if(!enqueue(*s, x != vv, expl_thunk { ex_x_ne_xi, this, vv - base }))
            return false;
        } else {
          z_supp |= y_supp;
          supp = end;
        }
      }

      if(z_supp.lb > z.lb()) {
        if(!z.set_lb(z_supp.lb, expl_thunk { ex_lb<ex_z_lb>, this, 0 }))
          return false;
      }

      if(z_supp.ub < z.ub()) {
        if(!z.set_ub(z_supp.ub, expl_thunk { ex_ub<ex_z_ub>, this, 1}))
          return false;
      }
       
      if(supp < end) {
        if(z_supp.lb > supp->lb()) {
          if(!supp->set_lb(z_supp.lb, expl_thunk { ex_lb<ex_y_lb>, this, (int) (supp - ys.begin()), expl_thunk::Ex_BTPRED }))
            return false;
        }
        if(z_supp.ub < supp->ub()) {
          if(!supp->set_ub(z_supp.ub, expl_thunk { ex_ub<ex_y_ub>, this, (int) (supp - ys.begin()), expl_thunk::Ex_BTPRED }))
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
    vec<int64_t> cut_hint;
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
