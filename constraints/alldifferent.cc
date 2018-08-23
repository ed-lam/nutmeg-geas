#ifndef PHAGE_ALLDIFFERENT_H
#define PHAGE_ALLDIFFERENT_H

#include "mtl/bool-set.h"
#include "engine/propagator.h"
#include "engine/propagator_ext.h"
#include "vars/intvar.h"

namespace geas {
  
class alldiff_v : public propagator, public prop_inst<alldiff_v> {
  watch_result wake(int xi) {
    fixed.push(xi);
    queue_prop();
    return Wt_Keep; 
  }
public:
  alldiff_v(solver_data* s, vec<intvar>& _xs)
    : propagator(s), xs(_xs) {
    for(int ii : irange(xs.size())) {
      if(is_fixed(xs[ii])) {
        // Kill the value in other vars
        intvar::val_t k(lb(xs[ii]));
        for(int jj : irange(xs.size())) {
          if(ii == jj) continue;
          if(in_domain(xs[jj], k)) {
            if(!enqueue(*s, xs[jj] != k, reason()))
              throw RootFail();
          }
        }
      } else {
        xs[ii].attach(E_FIX, watch<&P::wake>(ii, Wt_IDEM));
      }
    }
  }

  bool propagate(vec<clause_elt>& confl) {
    for(int xi : fixed) {
      intvar::val_t k(lb(xs[xi]));
      patom_t r(xs[xi] != k);
      assert(s->state.is_inconsistent(r));

      for(int ii : irange(xi)) {
        if(in_domain(xs[ii], k)) {
          if(!enqueue(*s, xs[ii] != k, r))
            return false;
        }
      }
      for(int ii : irange(xi+1, xs.size())) {
        if(in_domain(xs[ii], k)) {
          if(!enqueue(*s, xs[ii] != k, r))
            return false;
        }
      }
    }
    fixed.clear();

    return true;
  }

  void cleanup(void) {
    fixed.clear();
    is_queued = false;
  }

  vec<intvar> xs;

  vec<int> fixed;
};

// If the link points down, there's slack.
// If it points up, it's a union-find.
#if 0
struct tl_entry {
  int link;
  int cap;
};
struct timeline {
  int find(int k) {
    if(tl[k].link > k)
      return tl[k].link = find(tl[k].link);
    return k;
  }
  
  int extend(int k) {
    k = find(k);
    tl[k].cap -= 1;
    if(tl[k].cap) {
      return k;
    } else {

    }
  }

  vec<tl_entry> tl;
};

class alldiff_b : public propagator {
  typedef typename intvar::val_t val_t;

  static watch_result wake_lb(void* ptr, int xi) {
    alldiff_b* p(static_cast<alldiff_b*>(ptr)); 
    p->queue_prop();
    p->lb_change.add(xi);
    return Wt_Keep;
  }
  static watch_result wake_ub(void* ptr, int xi) {
    alldiff_b* p(static_cast<alldiff_b*>(ptr)); 
    p->queue_prop();
    p->ub_change.add(xi);
    return Wt_Keep;
  }

  public: 
    alldiff_b(solver_data* s, vec<intvar>& _vs)
      : propagator(s), vs(_vs) {
      for(int ii : irange(vs.size())) {
        vs[ii].attach(E_LB, watch_callback(wake_lb, this, ii));
        vs[ii].attach(E_UB, watch_callback(wake_ub, this, ii));
        lb_ord.push(ii);
        ub_ord.push(ii);
        lbs.push(lb(vs[ii]));
        ubs.push(lb(vs[ii]));
      }
    }

    void root_simplify(void) {
      return; 
    }

    void cleanup(void) {
      is_queued = false;
      lb_change.clear();
      ub_change.clear();
    }
    
    struct bound_cmp {
      bound_cmp(vec<val_t>& _bs)
        : bounds(_bs) { }

      bool operator()(int ii, int jj) {
        return bounds[ii] < bounds[jj];  
      }
      vec<val_t>& bounds;
    };

    bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running alldiff]]" << std::endl;
#endif
      
      for(int ii : irange(vs.size())) {
        lbs[ii] = lb(vs[ii]);
        ubs[ii] = ub(vs[ii]);
      }
      std::sort(lb_ord.begin(), lb_ord.end(), bound_cmp(lbs));
      std::sort(ub_ord.begin(), ub_ord.end(), bound_cmp(ubs));

      // Do some stuff here  

      return true;
    }

    int pathmax(int* p, int k) {
      while(k < p[k])
        k = p[k];  
      return k;
    }
    int pathset(int* p, int x, int y, int z) {
      do {
        o = p[x];
        p[x] = 
    }

    void setup(void) {
      // Collect the set of distinct bounds

    }
    
    // The algorithm, directly copied from 'A fast and simple algorithm
    // for bounds consistency of the alldifferent constraint'
    bool update_lb(void) {
      for (i = 1; i <= nb+1; i++) {
        t[i] = h[i] = i-1;
        d[i] = bounds[i] - bounds[i-1];
      }
      for (i = 0; i < niv; i++) {
        (x, y) = (maxsorted[i]->minrank, maxsorted[i]->maxrank)
        z = pathmax(t, x+1);
        j = t[z];
        if (--d[z] == 0) {
          t[z] = z+1;
          z = pathmax(t, t[z]);
          t[z] = j;
        }
        pathset(t, x+1, z, z);
        if (d[z] < bounds[z] - bounds[y])
          return false;
        if (h[x] > x) {
          w = pathmax(h, h[x]);
          if(!set_lb(xs[maxsorted[i].var], bounds[w], expl<&P::ex_lb>(maxsorted[i].var, expl_thunk::Ex_BTPRED)))
            return false;
          pathset(h, x, w, w);
        }
        if (d[z] == bounds[z] - bounds[y]) {
          pathset(h, h[y], j-1, y);
          h[y] = j-1;
        }
      }
      return true;
    }


    // Parameters
    vec<intvar> xs;

    // Temporary state
    vec<int> perm;

    vec<int> bounds;
    vec<int> t;
    vec<int> d;

      vec<val_t> lbs;
      vec<val_t> ubs;

      boolset lb_change;
      boolset ub_change;
};
#endif

bool all_different_int(solver_data* s, vec<intvar>& xs, patom_t r = at_True) {
  assert(r == at_True);

  return alldiff_v::post(s, xs);
}

}
#endif
