#include <algorithm>
#include <climits>
#include "engine/propagator.h"
#include "solver/solver_data.h"
#include "vars/intvar.h"
#include "mtl/bool-set.h"
#include "mtl/p-sparse-set.h"
#include "utils/interval.h"

// using max = std::max;
// using min = std::min;

namespace phage {

// Propagator:
// non-incremental, with naive eager explanations
class iprod : public propagator {
  static void wake_z(void* ptr, int xi) {
    iprod* p(static_cast<iprod*>(ptr)); 
    p->queue_prop();
  }

  static void wake_xs(void* ptr, int xi) {
    iprod* p(static_cast<iprod*>(ptr)); 
    p->queue_prop();
  }

public:
  iprod(solver_data* s, intvar _z, intvar _x, intvar _y)
    : propagator(s), z(_z), x(_x), y(_y)
  {
    z.attach(E_LU, watch_callback(wake_z, this, 0));
    x.attach(E_LU, watch_callback(wake_xs, this, 0));
    y.attach(E_LU, watch_callback(wake_xs, this, 1));
  }
  
  template<class T>
  void push_expl(int_itv iz, int_itv ix, int_itv iy, T& ex) {
    ex.push(z < iz.lb);
    ex.push(z > iz.ub);
    ex.push(x < ix.lb);
    ex.push(x > ix.ub);
    ex.push(y < iy.lb);
    ex.push(y > iy.ub);
  }

  clause* make_expl(int_itv iz, int_itv ix, int_itv iy) {
    expl_builder ex(s->persist.alloc_expl(7)); 
    push_expl(iz, ix, iy, ex);
    return *ex;
  }
  
  bool propagate(vec<clause_elt>& confl) {
    // Non-incremental propagator
#ifdef LOG_ALL
    std::cerr << "[[Running iprod]]" << std::endl;
#endif
    int_itv z_supp(var_unsupp(z));          
    int_itv x_supp(var_unsupp(x));
    int_itv y_supp(var_unsupp(y));

    int_itv z_itv(var_range(z));
    int_itv x_itv(var_range(x));
    int_itv y_itv(var_range(y));
    if(z_itv.elem(0)) {
      if(x_itv.elem(0)) {
        z_supp = int_itv { 0, 0 };
        y_supp = y_itv;
        x_supp = int_itv { 0, 0 };
      }
      if(y_itv.elem(0)) {
        z_supp = int_itv { 0, 0 };
        x_supp = x_itv;
        y_supp |= int_itv { 0, 0 };
      }
    }

    if(x_itv.ub > 0) {
      int_itv x_pos(pos(var_range(x)));
      if(y_itv.ub > 0) {
        // + * + 
        int_itv y_pos(pos(var_range(y)));
        int_itv xy { x_pos.lb * y_pos.lb, x_pos.ub * y_pos.ub };
        int_itv z_feas(z_itv & xy);
        if(!z_feas.empty()) {
          z_supp |= z_feas;
          // Propagate back to x, y
          x_supp |= (x_itv & int_itv {(z_feas.lb + y_pos.ub - 1)/ y_pos.ub,
                                      z_feas.ub / y_pos.lb});
          y_supp |= (y_itv & int_itv {(z_feas.lb + x_pos.ub - 1) / x_pos.ub,
                                      z_feas.ub / x_pos.lb});
        }
      }
      if(y_itv.lb < 0) {
        // + * -  
        int_itv y_neg(neg(var_range(y)));
        int_itv xy { x_pos.ub * y_neg.lb, x_pos.lb * y_neg.ub };
        int_itv z_feas(z_itv & xy);
        if(!z_feas.empty()) {
          z_supp |= z_feas;
          // Propagate back to x, y
          x_supp |= (x_itv & int_itv {z_feas.lb / y_neg.lb,
                                      (z_feas.ub + y_neg.ub + 1)/y_neg.ub});
          y_supp |= (y_itv & int_itv {z_feas.lb / x_pos.lb,
                                      (z_feas.ub - x_pos.ub + 1)/x_pos.ub});
        }
      }
    }
    if(x_itv.lb < 0) {
      int_itv x_neg(neg(var_range(x)));
      if(y_itv.ub > 0) {
        // - * +  
        int_itv y_pos(pos(var_range(y)));
        int_itv xy { x_neg.lb * y_pos.lb, x_neg.ub * y_pos.lb };
        int_itv z_feas(z_itv & xy);
        if(!z_feas.empty()) {
          z_supp |= z_feas;
          // Propagate back to x, y
          x_supp |= (x_itv & int_itv {z_feas.lb / y_pos.lb,
                                      (z_feas.ub - y_pos.ub + 1)/y_pos.ub});
          y_supp |= (y_itv & int_itv {(z_feas.ub + x_neg.ub + 1)/x_neg.ub,
                                      z_feas.lb / x_neg.lb});
        }
      }
      if(y_itv.lb < 0) {
        // - * - 
        int_itv y_neg(neg(var_range(y)));
        int_itv xy { x_neg.ub * y_neg.ub, x_neg.lb * y_neg.lb };
        int_itv z_feas(z_itv & xy);
        if(!z_feas.empty()) {
          z_supp |= z_feas;
          // Propagate back to x, y
          x_supp |= (x_itv & int_itv {z_feas.ub / y_neg.ub,
                                      (z_feas.lb+y_neg.lb+1)/ y_neg.lb});
          y_supp |= (y_itv & int_itv {z_feas.ub / x_neg.ub,
                                      (z_feas.lb+x_neg.lb+1)/ x_neg.lb});
        }
      }
    }

    if(z_supp.ub < z_supp.lb) {
      // Infeasible
      push_expl(z_itv, x_itv, y_itv, confl);
      return false;
    }
    assert(x_supp.lb <= x_supp.ub);
    assert(y_supp.lb <= y_supp.ub);

    if(z_supp.lb > z.lb()) {
      clause* cl(make_expl(z_itv, x_itv, y_itv));
      (*cl)[0] = (z >= z_supp.lb);
      if(!z.set_lb(z_supp.lb, cl))
        return false;
    }
    if(z_supp.ub < z.ub()) {
      clause* cl(make_expl(z_itv, x_itv, y_itv));
      (*cl)[0] = (z <= z_supp.ub);
      if(!z.set_lb(z_supp.lb, cl))
        return false;
    }
    if(x_supp.lb > x.lb()) {
      clause* cl(make_expl(z_itv, x_itv, y_itv));
      (*cl)[0] = (x >= x_supp.lb);
      if(!x.set_lb(x_supp.lb, cl))
        return false;
    }
    if(x_supp.ub < x.ub()) {
      clause* cl(make_expl(z_itv, x_itv, y_itv));
      (*cl)[0] = (x <= x_supp.ub);
      if(!x.set_ub(x_supp.ub, cl))
        return false;
    }
    if(y_supp.lb > y.lb()) {
      clause* cl(make_expl(z_itv, x_itv, y_itv));
      (*cl)[0] = (y >= y_supp.lb);
      if(!y.set_lb(y_supp.lb, cl))
        return false;
    }
    if(y_supp.ub < y.ub()) {
      clause* cl(make_expl(z_itv, x_itv, y_itv));
      (*cl)[0] = (y <= y_supp.ub);
      if(!y.set_ub(y_supp.ub, cl))
        return false;
    }

    return true;
  }

  bool check_sat(void) {
    return true;
  }

  void root_simplify(void) { }

  void cleanup(void) { is_queued = false; }

protected:
  intvar z;
  intvar x;
  intvar y;
};

irange pos_range(intvar z) { return irange(std::max(1, (int) z.lb()), z.ub()+1); }
irange neg_range(intvar z) { return irange(z.lb(), std::min(-1, (int) z.ub())); }

// Decomposition of z = x * y.
void imul_decomp(solver_data* s, intvar z, intvar x, intvar y) {
  // Establish lower bounds on abs(z).
  // Case splits. x pos:
  if(x.ub() > 0) {
    // y pos
    if(y.ub() > 0) {
      for(int kx : pos_range(x)) {
        for(int ky : pos_range(y)) {
          add_clause(s, x < kx, y < ky, z >= kx*ky);  
          add_clause(s, x > kx, y > ky, x < -kx, y < -ky, z <= kx*ky);
        }
      }
    }
    // y neg
    if(y.lb() < 0) {
      for(int kx : pos_range(x)) {
        for(int ky : neg_range(y)) {
          add_clause(s, x < kx, y > ky, z <= kx*ky);
          add_clause(s, x > kx, y < ky, x < -kx, y > -ky, z >= kx*ky);
        }
      }
    }
  }
  // x neg
  if(x.lb() < 0) {
    if(y.ub() > 0) {
      for(int kx : neg_range(x)) {
        for(int ky : pos_range(y)) {
          add_clause(s, x > kx, y < ky, z <= kx*ky);
          add_clause(s, x < kx, y > ky, x > -kx, y < -ky, z >= kx*ky);
        }
      }
    }
    if(y.lb() < 0) {
      for(int kx : neg_range(x)) {
        for(int ky : neg_range(y)) {
          add_clause(s, x > kx, y > ky, z >= kx*ky);
          add_clause(s, x < kx, y < ky, x > -kx, y > -ky, z <= kx*ky);
        }
      }
    }
  }
}

void int_mul(solver_data* s, intvar z, intvar x, intvar y) {
  // imul_decomp(s, z, x, y);
  new iprod(s, z, x, y);
}

class iabs : public propagator {
  static void wake(void* ptr, int xi) {
    iabs* p(static_cast<iabs*>(ptr)); 
    p->queue_prop();
  }

  // Explanation functions  
  // Annoyingly, for upper bounds, we need invert the
  // value manually.
  static void ex_z_lb(void* ptr, int sign,
                        pval_t val, vec<clause_elt>& expl) {
    iabs* p(static_cast<iabs*>(ptr));
    if(sign) {
      expl.push(p->x < to_int(val));
    } else {
      expl.push(p->x > -to_int(val));
    }
  }
  static void ex_z_ub(void* ptr, int _xi, pval_t val,
                        vec<clause_elt>& expl) {
    iabs* p(static_cast<iabs*>(ptr));
    int64_t ival(to_int(pval_max - val));

    expl.push(p->x > ival);
    expl.push(p->x < -ival);
  }

  static void ex_x_lb(void* ptr, int sign,
                        pval_t val, vec<clause_elt>& expl) {
    iabs* p(static_cast<iabs*>(ptr));
    int64_t ival(to_int(val));
    if(sign) {
      expl.push(p->x <= -ival);
      expl.push(p->z < ival);
    } else {
      expl.push(p->z > -ival);
    }
  }
  static void ex_x_ub(void* ptr, int sign,
                        pval_t val, vec<clause_elt>& expl) {
    iabs* p(static_cast<iabs*>(ptr));
    int64_t ival(to_int(pval_max - val));

    if(sign) {
      expl.push(p->z > ival);
    } else {
      expl.push(p->x >= -ival);
      expl.push(p->z < ival);
    }
  }

public:
  iabs(solver_data* s, intvar _z, intvar _x)
    : propagator(s), z(_z), x(_x)
  {
    z.attach(E_LU, watch_callback(wake, this, 0));
    x.attach(E_LU, watch_callback(wake, this, 1));
  }
 
  bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
    std::cerr << "[[Running iabs]]" << std::endl;
#endif
    // Case split
    int_itv z_itv { z.ub()+1, z.lb()-1 };
    int_itv x_itv { x.ub()+1, x.lb()-1 };
//    int z_min = z.ub()+1;
//    int z_max = z.lb()-1;

//    int x_min = x.ub()+1;
//    int x_max = x.lb()-1;

    if(x.lb() < 0) {
      int_itv neg { std::max(x.lb(), -z.ub()),
                    std::max(x.ub(), -z.lb()) };
      x_itv |= neg;
      z_itv |= -neg;
    }
    if(x.ub() >= 0) {
      int_itv pos { std::max(z.lb(), z.lb()),
                    std::min(x.ub(), z.ub()) }; 
      x_itv |= pos;
      z_itv |= pos;
    }

    if(z_itv.ub < z.ub()) {
      if(!z.set_ub(z_itv.ub, expl_thunk { ex_z_ub, this, 0 }))
        return false;
    }
    if(z_itv.lb > z.lb()) {
      if(!z.set_lb(z_itv.lb, expl_thunk { ex_z_lb, this, x_itv.lb >= 0 }))
        return false;
    }
    if(x_itv.ub < x.ub()) {
      if(!x.set_ub(x_itv.ub, expl_thunk { ex_x_ub, this, x_itv.ub >= 0 }))
        return false;
    }
    if(x_itv.lb > x.ub()) {
      if(!x.set_lb(x_itv.lb, expl_thunk { ex_x_lb, this, x_itv.lb >= 0}))
        return false;
    }
    return true;
#if 0
    int z_min = z.lb();
    if(x.lb() > -z_min) {
      // z = x
      if(z_min > x.lb()) {
        if(!x.set_lb(z_min, expl_thunk ex_x_lb, this, 1))
          return false;
      }
      if(z.ub() < x.ub()) {
         
      }
    } else if(x.ub() < z_min) {
      // z = -x
      
    }
#endif
    return true;
  }

  bool check_sat(void) {
    if(x.lb() <= 0) {
      int low = std::max((int) z.lb(), std::max(0, (int) -x.ub()));
      int high = std::min(z.ub(), -x.lb());
      if(low <= high)
        return true;
    }
    if(x.ub() >= 0) {
      int low = std::max((int) z.lb(), std::max(0, (int) x.lb()));
      int high = std::min(z.ub(), x.ub());
      if(low <= high)
        return true;
    }
    return false;
  }

  void cleanup(void) { is_queued = false; }

protected:
  intvar z;
  intvar x; 
};

// Only use for small domains
void iabs_decomp(solver_data* s, intvar z, intvar x) {
  // Set up initial bounds
  if(z.lb() < 0)
    z.set_lb(0, reason());
  if(x.lb() < -z.ub())
    x.set_lb(-z.ub(), reason());
  if(z.ub() < x.ub())
    x.set_ub(z.ub(), reason());

  for(int64_t k : z.domain()) {
    add_clause(s, x < -k, x > k, z <= k);
    add_clause(s, x > -k, z >= k);
    add_clause(s, x < k, z >= k);
  }
}

#if 0
// Non-incremental implementation. FIXME
class imax : public propagator {
  static void wake_z(void* ptr, int _k) {
    imax* p(static_cast<imax*>(ptr)); 
    p->queue_prop();     
  }
  static void wake_x(void* ptr, int xi) {
    imax* p(static_cast<imax*>(ptr)); 
    p->queue_prop();     
  }

public:
  imax(solver_data* s, intvar _z, vec<intvar>& _xs)
    : propagator(s), z(_z), xs(_xs) { 
    z.attach(E_LU, watch_callback(wake_z, this, 0));

    for(int ii = 0; ii < xs.size(); ii++)
      xs[ii].attach(E_LU, watch_callback(wake_x, this, ii));
  }
 
  bool propagate(vec<clause_elt>& confl) {
    std::cout << "[[Running imax]]" << std::endl;
    int lb = INT_MIN;
    int ub = INT_MIN;
    int z_ub = z.ub();
    for(intvar x : xs) {
      lb = std::max(lb, (int) x.lb()); 
      ub = std::max(ub, (int) x.ub());
      if(z_ub < x.ub()) {
        if(!x.set_ub(z_ub, z <= z_ub))
          return false;
      }
    }

    if(ub < z.ub()) {
      expl_builder c(s->persist.alloc_expl(1 + xs.size()));
      for(intvar x : xs) {
        c.push(x > ub); 
      }
      if(!z.set_ub(ub, *c))
        return false;
    }

    if(lb > z.lb()) {
      expl_builder c(s->persist.alloc_expl(1 + xs.size()));
      for(intvar x : xs) {
        c.push(x < lb);
      }

      if(!z.set_lb(lb, *c))
        return false;
    }

    return true;
  }

  bool check_sat(void) {
    int lb = INT_MIN; 
    int ub = INT_MIN;
    for(intvar x : xs) {
      lb = std::max(lb, (int) x.lb());
      ub = std::max(ub, (int) x.ub());
    }
    return lb <= z.ub() && z.lb() <= ub;
  }

  void root_simplify(void) { }

  void cleanup(void) { is_queued = false; }

protected:
  intvar z;
  vec<intvar> xs;
};

#else
// Incremental version
class imax : public propagator {
  static void wake_z(void* ptr, int k) {
    imax* p(static_cast<imax*>(ptr));
    p->z_change |= k;
    p->queue_prop();
  }

  static void wake_x(void* ptr, int xi) {
    imax* p(static_cast<imax*>(ptr));
    assert((xi>>1) < p->xs.size());
    if(xi&1) { // LB
      if(!p->lb_change.elem(xi>>1))
        p->lb_change.add(xi>>1);
      p->queue_prop();
    } else {
      if(xi>>1 == p->ub_supp)
        p->supp_change = E_UB;
    }
  }

  static void expl_z_lb(imax* p, int xi, pval_t v,
                          vec<clause_elt>& expl) {
    expl.push(p->xs[xi] >= to_int(v));
  }

  static void expl_z_ub(imax* p, int xi, pval_t v,
                          vec<clause_elt>& expl) {
    for(intvar x : p->xs) {
      expl.push(x <= to_int(v));
    }
  }

  static void expl_xi_lb(imax* p, int xi, pval_t v,
                          vec<clause_elt>& expl) {
    expl.push(p->z > to_int(v));
    for(int x : irange(xi)) {
      expl.push(p->xs[x] >= to_int(v));
    }
    for(int x : irange(xi+1,p->xs.size())) {
      expl.push(p->xs[x] >= to_int(v));
    }
  }

  static void expl_xi_ub(imax* p, int xi, pval_t v,
                          vec<clause_elt>& expl) {
    expl.push(p->z <= to_int(v));
  }

public:
  imax(solver_data* s, intvar _z, vec<intvar>& _xs)
    : propagator(s), z(_z), xs(_xs),
      z_change(0), supp_change(0) { 
    z.attach(E_LB, watch_callback(wake_z, this, 0));
    z.attach(E_UB, watch_callback(wake_z, this, 1));

    for(int ii = 0; ii < xs.size(); ii++) {
      xs[ii].attach(E_LB, watch_callback(wake_x, this, ii<<1));
      xs[ii].attach(E_UB, watch_callback(wake_x, this, (ii<<1)|1));
    }

    maybe_max.growTo(xs.size());
    for(int xi : irange(0, xs.size()))
      maybe_max.insert(xi);

    lb_change.growTo(xs.size()); 
  }

  inline void mm_remove(int k, bool& mm_trailed) {
    if(!mm_trailed)
      trail_push(s->persist, maybe_max.sz);
    mm_trailed = true;
    maybe_max.remove(k);
  }

  inline bool propagate_z_ub(vec<clause_elt>& confl, bool& mm_trailed) {
    unsigned int seen_var = ub_supp;
    int seen_ub = xs[ub_supp].ub();
    for(int xi : maybe_max) {
      assert(xi < xs.size());
      if(seen_ub < xs[xi].ub()) {
        seen_var = xi;
        seen_ub = xs[xi].ub();
      }
    }

    if(seen_ub < z.ub()) {
      expl_builder e(s->persist.alloc_expl(1 + xs.size()));
      for(intvar x : xs)
        e.push(x > seen_ub);
      if(!z.set_ub(seen_ub, *e))
        return false;
    }
    if(seen_var != ub_supp)
      trail_change(s->persist, ub_supp, seen_var);

    return true; 
  }

  inline bool propagate_xs_lb(vec<clause_elt>& confl, bool& mm_trailed) {
    unsigned int *xi = maybe_max.begin();
    int z_lb = z.lb();
    while(xi != maybe_max.end()) {
      if(xs[*xi].ub() < z_lb) {
        // xs[*xi] cannot be the maximum
        if(!mm_trailed) {
          mm_trailed = true;
          trail_push(s->persist, maybe_max.sz);
        }
        maybe_max.remove(*xi);
      } else {
        // lb(z) won't change anyway
        if(xs[*xi].lb() == z_lb)
          return true;

        goto first_lb_found;
      }
    }
    // Every variable is below lb_max.
    // Set up conflict and bail
    confl.push(z < z_lb);
    for(intvar x : xs)
      confl.push(x >= z_lb);
    return false;

first_lb_found:
    unsigned int supp = *xi;
    ++xi;
    while(xi != maybe_max.end()) {
      if(xs[*xi].ub() < z_lb) {
        if(!mm_trailed) {
          mm_trailed = true;
          trail_push(s->persist, maybe_max.sz);
        }
        maybe_max.remove(*xi);
      } else {
        // Second support found
        return true;
      }
    }
    // Exactly one support found
    assert(xs[supp].lb() < z_lb);
    expl_builder e(s->persist.alloc_expl(1 + xs.size()));
    e.push(z < z_lb);
    for(int ii = 0; ii < xs.size(); ii++) {
        if(ii != supp)
          e.push(xs[ii] >= z_lb);
    }
    if(!xs[supp].set_lb(z_lb, *e))
      return false;

    return true;
  }

  bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
    std::cout << "[[Running imax]]" << std::endl;
#endif
    bool maybe_max_trailed = false;
    
    // forall x, ub(x) <= ub(z).
    if(z_change&E_UB) {
      int z_ub = z.ub();
      for(int ii : maybe_max) {
        if(z_ub < xs[ii].ub()) {
          if(!xs[ii].set_ub(z_ub, z > z_ub))
            return false; 
        }
      }
    }

    // forall x, lb(z) >= lb(x).
    int z_lb = z.lb();
    for(int xi : lb_change) {
      if(xs[xi].lb() > z_lb) {
        z_lb = xs[xi].lb();
        if(!z.set_lb(z_lb, xs[xi] < z_lb))
          return false;
      }
    }

    if(supp_change&E_UB) {
      if(!propagate_z_ub(confl, maybe_max_trailed))
        return false;
    }

    if(z_change&E_LB) {
      // Identify if any variable LBs must change
      if(!propagate_xs_lb(confl, maybe_max_trailed))
        return false;
    }
    return true;
  }

  bool check_sat(void) {
    int lb = INT_MIN; 
    int ub = INT_MIN;
    for(intvar x : xs) {
      lb = std::max(lb, (int) x.lb());
      ub = std::max(ub, (int) x.ub());
    }
    return lb <= z.ub() && z.lb() <= ub;
  }

  void root_simplify(void) { }

  void cleanup(void) {
    z_change = 0;
    supp_change = 0;
    lb_change.clear();
    is_queued = false;
  }

protected:
  intvar z;
  vec<intvar> xs;

  // Persistent state
  unsigned int lb_supp;
  unsigned int ub_supp;
  p_sparseset maybe_max; // The set of vars (possibly) above lb(z)

  // Transient state
  char z_change;
  char supp_change;
  boolset lb_change;
};
#endif

// Avoids introducing 
class ine_bound : public propagator {
  enum Vtag { Var_X = 1, Var_Z = 2 };

  static void wake_fix(void* ptr, int k) {
    ine_bound* p(static_cast<ine_bound*>(ptr));
    p->new_fix |= k;
    p->queue_prop();
  }

  static void wake_bound(void* ptr, int k) {
    ine_bound* p(static_cast<ine_bound*>(ptr));
    if(p->fixed) 
      p->queue_prop();
  }

public:
  ine_bound(solver_data* s, intvar _z, intvar _x)
    : propagator(s), z(_z), x(_x),
      fixed(0) {
    z.attach(E_FIX, watch_callback(wake_fix, this, 0));
    z.attach(E_LU, watch_callback(wake_bound, this, 0));

    x.attach(E_FIX, watch_callback(wake_fix, this, 1));
    x.attach(E_LU, watch_callback(wake_bound, this, 1));
  }

  inline bool prop_bound(intvar a, intvar b) {
    int k = a.lb();
    if(b.lb() == k) {
      if(!b.set_lb(k+1, s->persist.create_expl(a < k, a > k, b < k)))
        return false;
    }
    if(b.ub() == k) {
      if(!b.set_ub(k-1, s->persist.create_expl(a < k, a > k, b > k)))
        return false;
    }
    return true;
  }

  bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
    std::cout << "[[Running ineq]]" << std::endl;
#endif
    trail_change(s->persist, fixed, (char) (fixed|new_fix));
    
    switch(fixed) {
      case Var_X:
        return prop_bound(x, z);
      case Var_Z:
        return prop_bound(z, x);
      default:
        if(z.lb() == x.lb()) {          
          int k = z.lb();
          vec_push(confl, z < k, z > k, x < k, x > k);
          return false;
        }
        return true;
    }

    return true;
  }

  bool check_sat(void) {
    int lb = std::min(z.lb(), x.lb());
    int ub = std::max(z.ub(), x.ub());
    return lb < ub;
  }

  void root_simplify(void) { }

  void cleanup(void) {
    new_fix = 0;
    is_queued = false;
  }

protected:
  intvar z;
  intvar x;

  // Persistent state
  char new_fix;

  // Transient state
  char fixed;
};

void imax_decomp(solver_data* s, intvar z, vec<intvar>& xs) {
  vec<clause_elt> elts;
  for(int k : irange(z.lb(), z.ub()+1)) {
    elts.clear();
    elts.push(z <= k);
    for(intvar x : xs) {
      add_clause(s, x < k, z >= k);
      elts.push(x > k);
    }
    add_clause(*s, elts);
  }
  
  elts.clear();
  for(intvar x : xs) {
    if(x.ub() > z.ub())
      x.set_ub(z.ub(), reason());
    elts.push(x >= z.lb());
  }
  add_clause(*s, elts);
}

void int_max(solver_data* s, intvar z, vec<intvar>& xs) {
  // FIXME: Choose whether to use propagator or decomposition
  // imax_decomp(s, z, xs);
  new imax(s, z, xs);
}

bool int_abs(solver_data* s, intvar z, intvar x) {
  // FIXME: Implement propagator when domains are large
  // iabs_decomp(s, z, x);
  if(z.lb() < 0) {
    if(!z.set_lb(0, reason ()))
      return false;
  }
  new iabs(s, z, x);
  return true;
}

// Half-reified disequality
bool int_neq(solver_data* s, patom_t r, intvar x, intvar y) {
  // if(x.is_small() || y.is_small()) {
  int64_t lb = std::max(x.lb(), y.lb());
  int64_t ub = std::min(x.ub(), y.ub());
  if(ub - lb < 200) {
    // for(int k : x.domain() & y.domain()) {
    for(int k : irange(lb, ub+1)) {
      // if(x.in_domain(k) && y.in_domain(k)) {
        if(!add_clause(s, ~r, x != k, y != k))
          return false;
      // }
    }
  } else {
    // FIXME
    assert(s->state.is_entailed_l0(r));
  }
  return true;
}

}
