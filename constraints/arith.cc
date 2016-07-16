#include "engine/propagator.h"
#include "solver/solver_data.h"
#include "vars/intvar.h"

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

// Incremental version
/*
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
    bool maybe_max_trailed = false;
    
    // ub of z dropped.
    if(z_change&E_UB) {
      int z_ub = z.ub();
      for(int ii : maybe_max) {
        if(z_ub < xs[ii].ub()) {
          if(!xs[ii].set_ub(z_ub, z > z_ub))
            return false; 
        }
      }
    }

    if(supp_change&E_UB) {
      int z_lb = z.lb();
      int z_ub = z.ub();
      int seen_ub = xs[ub_supp].ub();
      if(seen_ub < z_ub) {
        // Look for a new support
        unsigned int supp = ub_supp;
        unsigned int* xi = maybe_max.begin();
        while(xi != maybe_max.end()) {
          if(xs[*xi].ub() > seen_ub) {
            if(xs[*xi].ub() == z_ub) {
              trail_change(s->persist, ub_supp, *xi);
              goto ub_supp_found;
            }
            supp = *xi;
            seen_ub = xs[*xi].ub();
            ++xi;
          } else if(xs[*xi].lb() < z_lb) {
            if(!maybe_max_trailed) {
              maybe_max_trailed = true;
              trail_push(s->persist, maybe_max.sz);
            }
            maybe_max.remove(*xi);
          }
        }
        // No support for z_ub. Propagate new ub.
        if(supp != ub_supp)
          trail_change(s->persist, ub_supp, supp);
        clause* c = s->persist.alloc_expl(1 + xs.size());
        clause_elt* e = &(*c)[1];
        for(intvar x : xs) {
          *e = (x > z_ub);
          ++e;
        }
        c->sz = 1 + xs.size();
        if(!z.set_ub(seen_ub, c))
          return false;
      }
    }
ub_supp_found:

    if(z_change&E_LB) {
      // Update
      unsigned int *xi = maybe_max.begin();
      int z_lb = z.lb();
      while(xi != maybe_max.end()) {
        if(xs[*xi].ub() < z_lb) {
          // xs[*xi] cannot be the maximum
          if(!maybe_max_trailed) {
              maybe_max_trailed = true;
              trail_push(s->persist, maybe_max.sz);
          }
          maybe_max.remove(*xi);
        } else {
          // Possibly equal to max
          if(xs[*xi].lb() == z_lb)
            goto lb_supported;

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
        if(!maybe_max_trailed) {
          maybe_max_trailed = true;
          trail_push(s->persist, maybe_max.sz);
        }
        maybe_max.remove(*xi);
      } else {
        // Second support found
        goto lb_supported; 
      }
    }
    // Exactly one support found
    if(z_lb < xs[supp].lb()) {
      int new_lb = xs[supp].lb();
      clause* c = s->persist.alloc_clause(1 + xs.size());
      clause_elt* e = &(*c)[1];
      for(int ii = 0; ii < xs.size(); ii++) {
        if(ii == supp) {
          (*e)++ = (x < new_lb);
        }
      }
      c->sz = e - c->begin();

      z.set_lb(new_lb, c);
    }

lb_supported:
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
    z_change = E_None;
    supp_change = E_None;
    is_queued = false;
  }

protected:
  intvar z;
  vec<intvar> xs;

  // Persistent state
  unsigned int lb_supp;
  unsigned int ub_supp;
  p_sparseset maybe_max; // The set of vars above lb(z)

  // Transient state
  intvar_event z_change;
  intvar_event supp_change;
};
*/

void int_max(solver_data* s, intvar z, vec<intvar>& xs) {
  // FIXME: Choose whether to use propagator or decomposition
  new imax(s, z, xs);
}

}
