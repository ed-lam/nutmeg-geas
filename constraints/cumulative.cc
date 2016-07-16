#include "solver/solver_data.h"
#include "engine/propagator.h"
#include "constraints/builtins.h"

#include "mtl/bool-set.h"
namespace phage {

class cumul_prop : public propagator {
  enum LimT { E_Start = 0, L_Start = 1, E_End = 2, L_End = 3, LimCount = 4};

/*
  struct lim_t {
    lim_t(LimT _kind, int _var, int _pred, int _succ)
      : kind(_kind), var(_var), pred(_pred), succ(_succ) { }
    LimT kind;
    int var; 
    int pred;
    int succ;  
  };
  */

  // Location of a landmark
  int loc(int key) const {
    int kind = key&3;
    int var = key>>2;
    switch(kind) {
      case E_Start:
        return starts[var].lb();
      case L_Start:
        return starts[var].ub();
      case E_End:
        return starts[var].lb() + duration[var];
      case L_End:
        return starts[var].ub() + duration[var];
      default:
        ERROR;
        return 0;
    }
  }

  struct key_cmp {
    key_cmp(cumul_prop* _p)
      : p(_p) { }
    bool operator()(int x, int y) const {
      return p->loc(x) < p->loc(y);
    }
    cumul_prop* p;
  };
  
public:
  cumul_prop(solver_data* s,
    vec<intvar>& ss, vec<int>& ds, vec<int>& rs, int c)
    : propagator(s), starts(ss), duration(ds), resource(rs), cap(c) {
    // Compute the order of endpoints
    int num_keys = starts.size()*LimCount;
    vec<int> keys;
    for(int ii = 0; ii < num_keys; ii++)
      keys.push(ii);
    
    key_cmp cmp(this);
    std::sort(keys.begin(), keys.end(), cmp);

    // Now initialize the linked-list
    pred.growTo(num_keys);
    succ.growTo(num_keys);
    pred[keys[0]] = keys[0];
    for(int ki = 1; ki < keys.size(); ki++) {
      pred[keys[ki]] = keys[ki-1];
      succ[keys[ki-1]] = keys[ki];
    }
    succ[keys.last()] = keys.last();
    
    hd = keys[0];
    tl = keys.last();

    cap_profile.growTo(starts.size());

    // Then walk along the list, initializing the compulsory
    // execution profile.
    boolset closed(starts.size());
    // Won't process the last key (tl), but that should be okay.
    int prof = 0;
    for(int ki = hd; succ[ki] != ki; ki = succ[ki]) {
      int var = ki>>2;
      int kind = ki&3;
      switch(kind) {
      case L_Start:
        if(!closed.elem(var)) {
          prof += resource[var];
          cap_profile[var] = prof;
        }
        break;
      case E_End:
        if(cap_profile[var] > 0)
          prof -= resource[var];
        closed.add(var);
        break;
      case E_Start:
      case L_End:
      default:
        break;
      }
    }
  }

  bool propagate(vec<clause_elt>& confl) {
    return true; 
  }

  bool check_sat(void) {
    // Revise changed resource capacities, and
    // check the compulsory profile is feasible
    return true;
  }

  void root_simplify(void) {
      
  }
  void cleanup(void) {
    is_queued = false;
    lb_change.clear();
    ub_change.clear();
  }

  // Constraint data
  vec<intvar> starts;
  vec<int> duration;
  vec<int> resource;
  int cap;

  // Persistent state
  int hd;
  int tl;
  vec<int> cap_profile;
  vec<int> pred;
  vec<int> succ;

  // Temporary state
  boolset lb_change;
  boolset ub_change;
};

void cumulative(solver_data* s,
  vec<intvar>& starts, vec<int>& duration, vec<int>& resource, int cap) {
  NOT_YET;
}

}
