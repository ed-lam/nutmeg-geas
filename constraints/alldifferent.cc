#ifndef PHAGE_ALLDIFFERENT_H
#define PHAGE_ALLDIFFERENT_H
#include <numeric>

#include "mtl/bool-set.h"
#include "utils/ordered-perm.h"
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

class alldiff_b : public propagator, public prop_inst<alldiff_b> {
  typedef typename intvar::val_t val_t;

  watch_result wake_lb(int xi) {
    queue_prop();
    // lb_low = std::min(lb_low, xs[xi].lb(s->wake_vals));
    return Wt_Keep;
  }
  watch_result wake_ub(int xi) {
    queue_prop();
    // ub_high = std::max(ub_high, xs[xi].ub(s->wake_vals));
    return Wt_Keep;
  }
  
  // Totally naive explanation: everything
  void ex_lb(int xi, pval_t p, vec<clause_elt>& expl) {
    for(int yi = 0; yi < xs.size(); ++yi) {
      expl.push(xs[yi] < lb(xs[yi]));
      expl.push(xs[yi] > ub(xs[yi]));
    }
  }

  void ex_ub(int xi, pval_t p, vec<clause_elt>& expl) {
    for(int yi = 0; yi < xs.size(); ++yi) {
      expl.push(xs[yi] < lb(xs[yi]));
      expl.push(xs[yi] > ub(xs[yi]));
    }
  }


  public: 
    alldiff_b(solver_data* s, vec<intvar>& _vs)
      : propagator(s), xs(_vs)
      , by_lb(s, xs.begin(), xs.end()), by_ub(s, xs.begin(), xs.end())
      , bounds(new int[2 * xs.size() + 2])
      , d(new int[2 * xs.size() + 2])
      , t(new int[2 * xs.size() + 2])
      , h(new int[2 * xs.size() + 2])
      , minrank(new int[xs.size()])
      , maxrank(new int[xs.size()])
      // , lb_low(INT_MIN), ub_high(INT_MAX)
    {
      for(int ii : irange(xs.size())) {
        xs[ii].attach(E_LB, watch<&P::wake_lb>(ii));
        xs[ii].attach(E_UB, watch<&P::wake_ub>(ii));
      }
      queue_prop();
    }
    ~alldiff_b(void) {
      delete[] bounds;
      delete[] d;
      delete[] h;
      delete[] minrank;
      delete[] maxrank;
    }

    void root_simplify(void) {
      return; 
    }

    void cleanup(void) {
      is_queued = false;
      /*
      lb_low = INT_MAX;
      ub_high = INT_MIN;
      */
    }

    // Totally dumb satisfiability checker: for each pair of interesting end-points,
    // count the number of definitely within.
    bool check_sat(ctx_t& ctx) {
      // fprintf(stderr, "%% Checking alldiff_b.\n");
      vec<int> starts;
      vec<int> ends;
      for(intvar x : xs) {
        starts.push(x.lb(s));
        ends.push(x.ub(s)+1);
      }
      std::sort(starts.begin(), starts.end());
      std::sort(ends.begin(), ends.end());
      
      int* ss(starts.begin()); 
      int* se(starts.end());
      for(int en : ends) {
        // Find the range of starts left of e.
        while(ss != se && (*ss) < en)
          ++ss;
        int* sb(starts.begin());
        for(; sb != ss; ++sb) {
          int st(*sb);
          // Count the number of variables with within [st,en].
          int c(std::accumulate(xs.begin(), xs.end(), 0,
            [&ctx,st,en](int acc, const intvar& x) { return acc + ((st <= x.lb(ctx) && x.ub(ctx) < en) ? 1 : 0); }));
          // If so, fail.
          if(en - st < c)
            return false;
        }
      }
      return true;
    }
    bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); }
    

    bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running alldiff]]" << std::endl;
#endif
      setup();
      
#if 0
      fprintf(stderr, "%% Alldiff bounds:");
      for(unsigned int xi : irange(xs.size())) {
        fprintf(stderr, " x%d: [%d, %d]", xi, (int) xs[xi].lb(s), (int) xs[xi].ub(s));        
      }
      fprintf(stderr, "\n");
#endif

      if(!update_lb(confl))
        return false;        
      if(!update_ub(confl))
        return false;
      /*
      for(int ii : irange(xs.size())) {
        lbs[ii] = lb(xs[ii]);
        ubs[ii] = ub(xs[ii]);
      }
      std::sort(lb_ord.begin(), lb_ord.end(), bound_cmp(lbs));
      std::sort(ub_ord.begin(), ub_ord.end(), bound_cmp(ubs));
      */

      return true;
    }

    static int pathmax(int* p, int k) {
      while(k < p[k])
        k = p[k];
      return k;
    }
    static int pathmin(int* p, int k) {
      while(k > p[k])
        k = p[k];
      return k;
    }
    static void pathset(int* a, int x, int y, int z) {
      int o = a[x];
      while(x != y) {
        a[x] = z;
        x = o;
        o = a[x];
      }
    }

    void setup(void) {
      const vec<unsigned int>& lb_ord(by_lb.get());
      const vec<unsigned int>& ub_ord(by_ub.get());
      
      int b(lb(xs[lb_ord[0]]));
      bounds[0] = b-1;
      bounds[1] = b;
      nb = 1;
      unsigned int* u_it(ub_ord.begin());
      int u_b(ub(xs[*u_it])+1);
      // Process the 
      for(unsigned int ii : lb_ord) {
        int l_i(lb(xs[ii]));
        // Process any upper bounds which are _strictly_ below the next lb.
        while(u_b < l_i) {
          if(b < u_b) {
            ++nb;
            bounds[nb] = b = u_b;
          }
          maxrank[*u_it] = nb;
          ++u_it;
          u_b = ub(xs[*u_it])+1;
        }
        // And now do the lb.
        if(b < l_i) {
          ++nb;
          bounds[nb] = b = l_i;
        }
        minrank[ii] = nb;
      }
      // Now process the remaining upper bounds.
      for(; u_it != ub_ord.end(); ++u_it) {
        u_b = ub(xs[*u_it])+1;
        if(b < u_b) {
          ++nb;
          bounds[nb] = b = u_b;
        }
        maxrank[*u_it] = nb;
      }
      bounds[nb+1] = u_b+1;
    }

    bool update_lb(vec<clause_elt>& confl) {
      // Assumes setup() has been called.

      // Initialize the timeline
      for(int i = 1; i <= nb+1; i++) {
        t[i] = h[i] = i-1;  
        d[i] = bounds[i] - bounds[i-1];
      }
      
      const vec<unsigned int>& ord(by_ub.get());
      for(unsigned int i : ord) {
        int x = minrank[i];
        int y = maxrank[i];
        int z = pathmax(t, x+1);
        int j = t[z];
        if(--d[z] == 0) {
          t[z] = z+1;
          z = pathmax(t, t[z]);
          t[z] = j;
        }
        pathset(t, x+1, z, z);
        if(d[z] < bounds[z] - bounds[y]) {
          // Set up conflict. We've been working by increasing ub, so 
          // bounds[y] is the right bound of a hall interval.
#if 0
          int hallmin = bounds[t[z]];
          int hallmax = bounds[y];
          int delta = 1 + hallmax - hallmin;
          assert(delta > 0);
          confl.clear();
          for(intvar x : xs) {
            if(hallmin <= x.lb(s) && x.ub(s) < hallmax) {
              confl.push(x < hallmin);
              confl.push(x >= hallmax);
              --delta;
              if(!delta)
                return false;
            }
          }
          ERROR;
#else
          // Process by _decreasing_ lower bound, to collect
          // the smallest suitable hall set.
          int hallmax = bounds[y]; 
          const vec<unsigned int>& hord(by_lb.get());
          unsigned int count = 0;
          vec<unsigned int> mem;
          for(int ii = hord.size()-1; ii >= 0; --ii) {
            int xi(hord[ii]);
            if(hallmax <= ub(xs[xi]))
              continue;
            mem.push(xi);
            ++count;
            if(hallmax - lb(xs[xi]) < count) {
              // Found our hall set.
              int hallmin = lb(xs[xi]);
              for(int yi : mem) {
                confl.push(xs[yi] < hallmin);
                confl.push(xs[yi] >= hallmax);
              }
              return false;
            }
          }
          ERROR;
#endif
        }
        if(h[x] > x) {
          int w = pathmax(h, h[x]);
          // maxsorted[i]->min = bounds[w];
          if(!set_lb(xs[i], bounds[w], expl<&P::ex_lb>(i, expl_thunk::Ex_BTPRED)))
            return false;
          pathset(h, x, w, w);
          h[y] = j-1;
        }
      }
      return true;
    }

    bool update_ub(vec<clause_elt>& confl) {
      // Assumes setup() has been called.

      // Initialize the timeline
      for(int i = 0; i <= nb; i++) {
        t[i] = h[i] = i+1;  
        d[i] = bounds[i+1] - bounds[i];
      }
      
      // Process by _decreasing_ lb.
      const vec<unsigned int>& ord(by_lb.get());
      for(int p = ord.size()-1; p >= 0; --p) {
        unsigned int i = ord[p];

        int x = minrank[i];
        int y = maxrank[i];
        int z = pathmin(t, y-1);
        int j = t[z];
        if(--d[z] == 0) {
          t[z] = z-1;
          z = pathmin(t, t[z]);
          t[z] = j;
        }
        pathset(t, y-1, z, z);
        if(d[z] < bounds[x] - bounds[z]) {
          // Set up conflict. Because we're processing by
          // decreasing lb, bounds[x] is the left bound of the hall interval.
          int hallmin = bounds[x];
#if 0
          int hallmax = bounds[t[z]];
          int delta = 1 + hallmax - hallmin;
          assert(delta > 0);
          confl.clear();
          for(intvar x : xs) {
            if(hallmin <= x.lb(s) && x.ub(s) < hallmax) {
              confl.push(x < hallmin);
              confl.push(x >= hallmax);
              --delta;
              if(!delta)
                return false;
            }
          }
#else
          // Process bounds by increasing ub, to collet the smallest over-full interval.
          unsigned int count = 0;
          vec<unsigned int> mem;
          for(int xi : by_ub.get()) {
            if(lb(xs[xi]) < hallmin)
              continue;
            count++;
            mem.push(xi);
            if(ub(xs[xi]) - hallmin + 1 < count) {
              // Found an interval
              int hallmax = ub(xs[xi]);
              for(int yi : mem) {
                confl.push(xs[yi] < hallmin);
                confl.push(xs[yi] > hallmax);
              }
              return false;
            }
          }
#endif
          ERROR;
        }
        if(h[y] < y) {
          int w = pathmin(h, h[y]);
          // maxsorted[i]->min = bounds[w];
          if(!set_ub(xs[i], bounds[w]-1, expl<&P::ex_ub>(i, expl_thunk::Ex_BTPRED)))
            return false;
          pathset(h, x, w, w);
          h[x] = j+1;
        }
      }
      return true;
    }

    // Parameters
    vec<intvar> xs;

    // Persistent state
    OrderedPerm< By_LB<intvar> > by_lb;
    OrderedPerm< By_UB<intvar> > by_ub;
    // Transient state
    int nb;
    int* bounds; // Has capacity 2 * |Vars| + 2
    int* d; // Critical capacity deltas
    int* t; // Critical capacity pointers
    int* h; // Hall interval pointers
    // Capacity |Vars|
    int* minrank;
    int* maxrank;
    /*
    vec<int> bounds;
    vec<int> t;
    vec<int> d;

    vec<val_t> lbs;
    vec<val_t> ubs;
    */
    // We're only interested in landmarks 
    /*
    int lb_low;
    int ub_high;
    */
    // Cached explanation information
};

bool all_different_int(solver_data* s, vec<intvar>& xs, patom_t r = at_True) {
  assert(r == at_True);

  return alldiff_b::post(s, xs);
  // return alldiff_v::post(s, xs);
}

}
#endif
