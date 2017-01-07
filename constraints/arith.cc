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
  static watch_result wake_z(void* ptr, int xi) {
    iprod* p(static_cast<iprod*>(ptr)); 
    p->queue_prop();
    return Wt_Keep;
  }

  static watch_result wake_xs(void* ptr, int xi) {
    iprod* p(static_cast<iprod*>(ptr)); 
    p->queue_prop();
    return Wt_Keep;
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

bool int_mul(solver_data* s, intvar z, intvar x, intvar y, patom_t r) {
  // imul_decomp(s, z, x, y);
  if(!s->state.is_entailed_l0(r))
    WARN("Half-reified int_mul not yet implemented.");
  new iprod(s, z, x, y);
  return true;
}

class iabs : public propagator {
  static watch_result wake(void* ptr, int xi) {
    iabs* p(static_cast<iabs*>(ptr)); 
    p->queue_prop();
    return Wt_Keep;
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
    intvar::val_t ival(to_int(pval_max - val));

    expl.push(p->x > ival);
    expl.push(p->x < -ival);
  }

  static void ex_x_lb(void* ptr, int sign,
                        pval_t val, vec<clause_elt>& expl) {
    iabs* p(static_cast<iabs*>(ptr));
    intvar::val_t ival(to_int(val));
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
    intvar::val_t ival(to_int(pval_max - val));

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

  for(intvar::val_t k : z.domain()) {
    add_clause(s, x < -k, x > k, z <= k);
    add_clause(s, x > -k, z >= k);
    add_clause(s, x < k, z >= k);
  }
}

// Incremental version
class imax : public propagator, public prop_inst<imax> {
  static watch_result wake_z(void* ptr, int k) {
    imax* p(static_cast<imax*>(ptr));
    p->z_change |= k;
    p->queue_prop();
    return Wt_Keep;
  }

  static watch_result wake_x(void* ptr, int xi) {
    imax* p(static_cast<imax*>(ptr));
    assert((xi>>1) < p->xs.size());
    if(xi&1) { // UB
      if(xi>>1 == p->ub_supp) {
        p->supp_change = E_UB;
        p->queue_prop();
      }
    } else {
      if(!p->lb_change.elem(xi>>1))
        p->lb_change.add(xi>>1);
      p->queue_prop();
    }
    return Wt_Keep;
  }

  static void expl_z_lb(imax* p, int xi, intvar::val_t v,
                          vec<clause_elt>& expl) {
    expl.push(p->xs[xi] < v);
  }

  static void expl_z_ub(imax* p, int xi, intvar::val_t v,
                          vec<clause_elt>& expl) {
    for(intvar x : p->xs) {
      expl.push(x > v);
    }
  }

  static void expl_xi_lb(imax* p, int xi, intvar::val_t v,
                          vec<clause_elt>& expl) {
    expl.push(p->z < v);
    for(int x : irange(xi)) {
      expl.push(p->xs[x] >= v);
    }
    for(int x : irange(xi+1,p->xs.size())) {
      expl.push(p->xs[x] >= v);
    }
  }

  static void expl_xi_ub(imax* p, int xi, intvar::val_t v,
                          vec<clause_elt>& expl) {
    expl.push(p->z > v);
  }

public:
  imax(solver_data* s, intvar _z, vec<intvar>& _xs)
    : propagator(s), z(_z), xs(_xs),
      z_change(0), supp_change(0) { 
    z.attach(E_LB, watch_callback(wake_z, this, 0, true));
    z.attach(E_UB, watch_callback(wake_z, this, 1, true));

    lb_supp = ub_supp = 0;
    int lb = xs[lb_supp].lb();
    int ub = xs[ub_supp].ub();
    for(int ii = 0; ii < xs.size(); ii++) {
      if(xs[ii].lb() < lb) {
        lb_supp = ii;
        lb = xs[ii].lb();
      }
      if(xs[ii].ub() > ub) {
        ub_supp = ii;
        ub = xs[ii].ub();
      }
      xs[ii].attach(E_LB, watch_callback(wake_x, this, ii<<1, true));
      xs[ii].attach(E_UB, watch_callback(wake_x, this, (ii<<1)|1, true));
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
      /*
      expl_builder e(s->persist.alloc_expl(1 + xs.size()));
      for(intvar x : xs)
        e.push(x > seen_ub);
      if(!z.set_ub(seen_ub, *e))
        */
      if(!z.set_ub(seen_ub, ex_thunk(ex_ub<expl_z_ub>, 0)))
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
    /*
    expl_builder e(s->persist.alloc_expl(1 + xs.size()));
    e.push(z < z_lb);
    for(int ii = 0; ii < xs.size(); ii++) {
        if(ii != supp)
          e.push(xs[ii] >= z_lb);
    }
    if(!xs[supp].set_lb(z_lb, *e))
    */
    if(!xs[supp].set_lb(z_lb, ex_thunk(ex_lb<expl_xi_lb>, supp)))
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
          // if(!xs[ii].set_ub(z_ub, z > z_ub))
          if(!xs[ii].set_ub(z_ub, ex_thunk(ex_ub<expl_xi_ub>, ii)))
            return false; 
        }
      }
    }

    // forall x, lb(z) >= lb(x).
    int z_lb = z.lb();
    for(int xi : lb_change) {
      if(xs[xi].lb() > z_lb) {
        z_lb = xs[xi].lb();
        // if(!z.set_lb(z_lb, xs[xi] < z_lb))
        if(!z.set_lb(z_lb, ex_thunk(ex_lb<expl_z_lb>, xi)))
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

// Avoids introducing 
class ine_bound : public propagator {
  enum Vtag { Var_X = 1, Var_Z = 2 };

  static watch_result wake_fix(void* ptr, int k) {
    ine_bound* p(static_cast<ine_bound*>(ptr));
    p->new_fix |= k;
    p->queue_prop();
    return Wt_Keep;
  }

  static watch_result wake_bound(void* ptr, int k) {
    ine_bound* p(static_cast<ine_bound*>(ptr));
    if(p->fixed) 
      p->queue_prop();
    return Wt_Keep;
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

bool int_max(solver_data* s, intvar z, vec<intvar>& xs, patom_t r) {
  // FIXME: Choose whether to use propagator or decomposition
  // imax_decomp(s, z, xs);
  if(!s->state.is_entailed_l0(r))
    WARN("Half-reified int_max not yet implemented.");

  new imax(s, z, xs);
  return true;
}

bool int_abs(solver_data* s, intvar z, intvar x, patom_t r) {
  // FIXME: Implement propagator when domains are large
  // iabs_decomp(s, z, x);
  if(!s->state.is_entailed_l0(r))
    WARN("Half-reified int_abs not yet implemented.");

  if(z.lb() < 0) {
    if(!z.set_lb(0, reason ()))
      return false;
  }
  new iabs(s, z, x);
  return true;
}

// Half-reified disequality
bool int_neq(solver_data* s, intvar x, intvar y, patom_t r) {
  // if(x.is_small() || y.is_small()) {
  intvar::val_t lb = std::max(x.lb(), y.lb());
  intvar::val_t ub = std::min(x.ub(), y.ub());
  if(ub - lb < 200) {
    // FIXME
    for(int k : irange(lb, ub+1)) {
      if(!add_clause(s, ~r, x != k, y != k))
        return false;
    }
  } else {
    // FIXME
    assert(s->state.is_entailed_l0(r));
  }
  return true;
}

class pred_le_hr : public propagator, public prop_inst<pred_le_hr> {
  enum { gen_mask = ~(1<<31) };
  enum status { S_Active = 1, S_Red = 2 };
  enum mode { P_None = 0, P_LB = 1, P_UB = 2, P_LU = 3, P_Deact = 4 };

  // Misc helper functions
  inline bool watch_expired(int xi) {
    return ((unsigned int) xi)>>1 != fwatch_gen;
  }
  inline pval_t choose_cut(void) {
    return pred_lb(s, x) + (pred_ub(s, y) - pred_lb(s, x))/2;
  }
  // inline pval_t lb(int pi) { return pred_lb(s, pi); }
  // inline pval_t ub(int pi) { return pred_ub(s, pi); }
  inline spval_t lb(int pi) { return pred_lb(s, pi); }
  inline spval_t ub(int pi) { return pred_ub(s, pi); }

  // Deactivation triggers
  watch_result wake_fail(int xi) {
    // If this is an expired watch, drop it.
    if(watch_expired(xi))
      return Wt_Drop;
    // If the propagator is already enabled,
    // ignore this.
    if(state&S_Active)
      return Wt_Keep;

    // Enqueue the propagator, to set ~r
    if(lb(x) > ub(y) + k) {
      mode = P_Deact;
      queue_prop();
      return Wt_Keep;
    }
    
    // Otherwise, find replacement watches
    // GKG: What's a good strategy?
    fwatch_gen = (fwatch_gen+1)&gen_mask;
    pval_t cut = choose_cut();
    attach(s, ge_atom(x, cut+1), watch<&P::wake_fail>(fwatch_gen<<1, Wt_IDEM));
    attach(s, le_atom(y, cut-1), watch<&P::wake_fail>((fwatch_gen<<1)|1, Wt_IDEM));
    return Wt_Keep;
  }

  watch_result wake_r(int _xi) {
    if(state & S_Red)
      return Wt_Keep;
    
    // If the constraint is activated, add watches on lb(x) and ub(y).
    if(!attached[0]) {
      s->pred_callbacks[x].push(watch<&P::wake_xs>(0, Wt_IDEM));
      attached[0] = true;
    }
    if(!attached[1]) {
      s->pred_callbacks[y^1].push(watch<&P::wake_xs>(1, Wt_IDEM));
      attached[1] = true;
    }

    trail_change(s->persist, state, (char) S_Active);
    mode = P_LU;
    queue_prop();
    return Wt_Keep;
  }

  watch_result wake_xs(int xi) {
    if(state&S_Red)
      return Wt_Keep;
    // If we've backtracked beyond the activation,
    // drop the watcher.
    if(!(state&S_Active)) {
      attached[xi] = false;
      return Wt_Drop;
    }
    mode |= xi ? P_UB : P_LB; 
    queue_prop();
    return Wt_Keep;
  }

  static void ex_r(void* ptr, int sep, pval_t _val,
    vec<clause_elt>& expl) {
    pred_le_hr* p(static_cast<pred_le_hr*>(ptr));
    vec_push(expl, le_atom(p->x, sep-1), ge_atom(p->y, sep - p->k));
  }

  static void ex_var(void* ptr, int var,
                        pval_t val, vec<clause_elt>& expl) {
    pred_le_hr* p(static_cast<pred_le_hr*>(ptr));
    expl.push(~(p->r));
    if(var) {
      expl.push(le_atom(p->x, val + p->k - 1));
    } else {
      expl.push(ge_atom(p->y, pval_inv(val) - p->k + 1));
    }
  }
public:
  pred_le_hr(solver_data* s, pid_t _x, pid_t _y, int _k, patom_t _r)
    : propagator(s), r(_r), x(_x), y(_y), k(_k), fwatch_gen(0),
       mode(P_None), state(0) {
    attached[0] = false; attached[1] = false;
    /*
    s->pred_callbacks[x].push(watch<&P::wake_xs>(0, Wt_IDEM));
    s->pred_callbacks[y^1].push(watch<&P::wake_xs>(1, Wt_IDEM));
    */
    // Pick an initial cut
//    x.attach(E_LB, watch_callback(wake_xs, this, 0, 1));
//    y.attach(E_UB, watch_callback(wake_xs, this, 1, 1));
    pval_t cut = choose_cut();
    attach(s, ge_atom(x, cut), watch<&P::wake_fail>(fwatch_gen<<1, Wt_IDEM));
    attach(s, le_atom(y, cut), watch<&P::wake_fail>((fwatch_gen<<1)|1, Wt_IDEM));

    attach(s, r, watch<&P::wake_r>(0, Wt_IDEM));
  }
  
  /*
  forceinline pval_t lb(pid_t p) { return s->state.p_vals[p]; }
  forceinline pval_t ub(pid_t p) { return pval_inv(s->state.p_vals[p^1]); }
  */
  
  bool propagate(vec<clause_elt>& confl) {
    // Non-incremental propagator
#ifdef LOG_ALL
    std::cerr << "[[Running ile]]" << std::endl;
#endif
    if(mode&P_Deact) {
      // Deactivation
      // sep = pred_lb(s, x);
      if(!enqueue(*s, ~r, ex_thunk(ex_r, 0))) {
        return false;
      }
      return true;
    }
    if(!state&S_Active)
      return true;

    if(mode&P_LB) {
      // FIXME: Overflow problems abound
      if(lb(x) > lb(y) + k) {
        if(!enqueue(*s, ge_atom(y, lb(x) - k), expl_thunk { ex_var, this, 1 }))
          return false;
      }
    }
    if(mode&P_UB) {
      if(ub(y) + k < ub(x)) {
        if(!enqueue(*s, le_atom(x, ub(y)+k), expl_thunk { ex_var, this, 0}))
          return false;
      }
    }
    return true;
  }

  void root_simplify(void) {
    if(ub(x) <= lb(y) + k || s->state.is_inconsistent(r)) {
      state = S_Red;
      return;
    }

    if(s->state.is_entailed(r)) {
      // FIXME: Instead, disable the propagator
      // and swap in a pred_le builtin.
      state = S_Active; 
    }
  }

  void cleanup(void) { mode = P_None; is_queued = false; }

protected:
  // Parameters
  patom_t r;
  pid_t x;
  pid_t y;
  int k;

  // Transient bookkeeping
  unsigned int fwatch_gen; // For watch expiration
  pval_t sep; // For explanation
  bool attached[2];

  // Persistent state
  char mode;
  char state;
};

/*
class ile_hr : public propagator {
  enum status { S_Active = 1, S_Red = 2 };

  static void wake_r(void* ptr, int _xi) {
    ile_hr* p(static_cast<ile_hr*>(ptr));
    if(p->state & S_Red)
      return;
    trail_change(p->s->persist, p->state, (char) S_Active);
    p->queue_prop();
  }

  static void wake_xs(void* ptr, int xi) {
    ile_hr* p(static_cast<ile_hr*>(ptr));
    if(p->state&S_Red)
      return;
    p->queue_prop();
  }

  static void ex_r(void* ptr, int sep, pval_t _val,
    vec<clause_elt>& expl) {
    ile_hr* p(static_cast<ile_hr*>(ptr));
    vec_push(expl, p->x < sep, p->y >= sep - p->k);
  }

  static void ex_var(void* ptr, int var,
                        pval_t val, vec<clause_elt>& expl) {
    ile_hr* p(static_cast<ile_hr*>(ptr));
    expl.push(~(p->r));
    if(var) {
      expl.push(p->x > to_int(val) + p->k);
    } else {
      expl.push(p->y < to_int(pval_inv(val)) - p->k);
    }
  }
public:
  ile_hr(solver_data* s, intvar _x, intvar _y, int _k, patom_t _r)
    : propagator(s), r(_r), x(_x), y(_y), k(_k) {
    x.attach(E_LB, watch_callback(wake_xs, this, 0, 1));
    y.attach(E_UB, watch_callback(wake_xs, this, 1, 1));
    attach(s, r, watch_callback(wake_r, this, 0, 1));
  }
  
  bool propagate(vec<clause_elt>& confl) {
    // Non-incremental propagator
#ifdef LOG_ALL
    std::cerr << "[[Running ile]]" << std::endl;
#endif
    if(state & S_Active) {
      if(x.lb() > y.lb() + k) {
        if(!y.set_lb(x.lb() - k, expl_thunk { ex_var, this, 1 }))
          return false;
      }
      if(y.ub() + k < x.ub()) {
        if(!x.set_ub(y.ub() + k, expl_thunk { ex_var, this, 0}))
          return false;
      }
    } else {
      if(x.lb() > y.ub() + k) {
        if(!enqueue(*s, ~r, expl_thunk { ex_r, this, (int) x.lb() }))
          return false;
        trail_change(s->persist, state, (char) S_Red);
      }
    }
    return true;
  }

  void root_simplify(void) {
    if(x.ub() <= y.lb() + k || s->state.is_inconsistent(r)) {
      state = S_Red;
      return;
    }

    if(s->state.is_entailed(r)) {
      state = S_Active; 
    }
  }

  void cleanup(void) { is_queued = false; }

protected:
  // Parameters
  patom_t r;
  intvar x;
  intvar y;
  int k;

  // Persistent state
  char state;
};
*/

bool pred_leq(solver_data* s, pid_t x, pid_t y, int k) {
  if(pred_ub(s, y) + k < pred_lb(s, x))
    return false;

  if(!enqueue(*s, ge_atom(y, pred_lb(s, x) - k), reason()))
    return false;
  if(!enqueue(*s, le_atom(x, pred_ub(s, y) + k), reason()))
    return false;

  s->infer.pred_ineqs[x].push({y, k});
  s->infer.pred_ineqs[y^1].push({x^1, k});
  return true;
}

bool int_leq(solver_data* s, intvar x, intvar y, int k) {
  return pred_leq(s, x.pid, y.pid, k);
  /*
  if(y.ub() + k < x.lb())
    return false;
  
  if(!enqueue(*s, y >= x.lb() - k, reason()))
    return false;
  if(!enqueue(*s, x <= y.ub() + k, reason()))
    return false;

  pid_t px = x.pid;
  pid_t py = y.pid;  
  s->infer.pred_ineqs[px].push({py, k});
  s->infer.pred_ineqs[py^1].push({px^1, k});
  return true;
  */
}

bool int_le(solver_data* s, intvar x, intvar y, int k, patom_t r) {
  if(s->state.is_entailed(r) && y.ub() + k < x.lb())
    return false;

  if(s->state.is_entailed(r))
    return int_leq(s, x, y, k);

  new pred_le_hr(s, x.pid, y.pid, k, r);
  return true;
}

bool pred_le(solver_data* s, pid_t x, pid_t y, int k, patom_t r) {
  if(s->state.is_entailed(r))
    return pred_leq(s, x, y, k);
  new pred_le_hr(s, x, y, k, r);
  return true;
}


}
