#include <climits>
#include "engine/propagator.h"
#include "solver/solver_data.h"
#include "vars/intvar.h"
#include "mtl/bool-set.h"
#include "mtl/p-sparse-set.h"

namespace phage {

// z = x * y
// Special case for fixed-sign
/*
template<int Sx, int Sy>
class int_mul_split : public propagator {
  enum { Sxy = (Sx*Sy) };
public:
  int_mul(solver_data* s, int_var _x, int_var _y, int_var _z)
    : propagator(s), x(_x), y(_y), z(_z)
  { }
 
  bool propagate(vec<clause_elt>& confl) {
    // Non-incremental propagator
    if(Sxy) {
      // Positive case: pick the smallest magnitudes
      int low_z =
        std::max(z.lb(), (Sx ? x.lb() : x.ub()) * (Sy ? y.lb() : y.ub()));
      int high_z =
        std::min(z.ub(), (Sx ? x.ub() : x.lb()) * (Sy ? y.ub() : y.lb()));

      int low_x =
        std::max(x.lb(),
          Sx ? ((low_z + y.ub()-1)/y.ub()) : (high_z/y.lb()));
      int high_x =
        std::min(x.ub(),
          Sx ? (high_z/y.lb()) : ((low_z - y.ub()+1)/y.ub()));

      int low_y =
        std::max(y.lb(),
          Sy ? ((low_z + x.ub()-1)/x.ub()) : (high_z/x.lb()));
      int high_y =
        std::min(y.ub(),
          Sy ? (high_z/x.lb()) : ((low_z - x.ub()+1)/x.ub()));
    } else {

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

class int_mul : public propagator {
public:
  int_mul(solver_data* s, int_var _x, int_var _y, int_var _z)
    : propagator(s), x(_x), y(_y), z(_z)
  { }
  
  typedef struct {
    int x[2];
  } range;


  bool propagate(vec<clause_elt>& confl) {
    // Non-incremental propagator
    
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

  // Temporary data
  range z_range;
  range x_range;
  range y_range;
};
*/

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
  imul_decomp(s, z, x, y);
}

class iabs : public propagator {
  iabs(solver_data* s, intvar _z, intvar _x)
    : propagator(s), z(_z), x(_x)
  { }
 
  bool propagate(vec<clause_elt>& confl) {
    int z_max = std::max(x.ub(), -x.lb());
    if(z_max < z.ub()) {
      if(!z.set_ub(z_max, s->persist.create_expl(x >= -z_max, x <= z_max)))
        return false;
    }

    int z_min = z.lb();
    if(x.lb() > -z_min) {
      // z = x
      if(z_min > x.lb()) {
        if(!x.set_lb(z_min, s->persist.create_expl(z >= z_min, x > -z_min)))
          return false;
      }
      if(z.ub() < x.ub()) {
        
      }
    } else if(x.ub() < z_min) {
      // z = -x
      
    }
    /*
    if(x.lb() < 0) {
      // Handle negative case

    }
    if(x.ub() > 0) {
      // Positive case
      z_min = 
    }
    */
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
    std::cout << "[[Running imax]]" << std::endl;
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

void int_abs(solver_data* s, intvar z, intvar x) {
  // FIXME: Implement propagator when domains are large
  iabs_decomp(s, z, x);
}

}
