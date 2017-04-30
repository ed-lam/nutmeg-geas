#include "engine/propagator.h"
#include "engine/propagator_ext.h"
#include "vars/intvar.h"
namespace phage {

class disj_int : public propagator {
  static watch_result wake(void* ptr, int xi) {
    disj_int* p(static_cast<disj_int*>(ptr)); 
    p->queue_prop();
    return Wt_Keep;
  }

  public: 
    disj_int(solver_data* s, vec<intvar>& _st, vec<int>& _du)
      : propagator(s), st(_st), du(_du) {
      for(int ii : irange(st.size())) {
        st[ii].attach(E_LU, watch_callback(wake, this, ii));
      }
      est.growTo(st.size());
      let.growTo(st.size());
    }

    void cleanup(void) {
      is_queued = false;
    }

    void root_simplify(void) {
      return; 
    }
    
    bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running disjunctive]]" << std::endl;
#endif
      
      // Timetable reasoning
      for(int ii : irange(st.size())) {
        est[ii] = st[ii].lb(s);
        let[ii] = st[ii].ub(s) + du[ii];
      }
        
      return true;
    }

    // Parameters
    vec<intvar> st; // Start times
    vec<int> du; // durations

    // Temporary storage
    vec<intvar::val_t> est; // earliest start time
    vec<intvar::val_t> let; // latest end time
};

class disj_var : public propagator {
  static watch_result wake_st(void* ptr, int xi) {
    disj_int* p(static_cast<disj_int*>(ptr)); 
    p->queue_prop();
    return Wt_Keep;
  }

  static watch_result wake_du(void* ptr, int xi) {
    disj_int* p(static_cast<disj_int*>(ptr)); 
    p->queue_prop();
    return Wt_Keep;
  }

  public: 
    disj_var(solver_data* s, vec<intvar>& _st, vec<intvar>& _du)
      : propagator(s), st(_st), du(_du) {
      for(int ii : irange(st.size())) {
        st[ii].attach(E_LU, watch_callback(wake_st, this, ii));
      }
      for(int ii : irange(du.size())) {
        du[ii].attach(E_LB, watch_callback(wake_du, this, ii));
      }
    }

    void root_simplify(void) {
      return; 
    }
    
    bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running disjunctive]]" << std::endl;
#endif
      
      return true;
    }

    // Parameters
    vec<intvar> st; // Start times
    vec<intvar> du; // durations

    // Temporary storage
};

void disjunctive_int(solver_data* s, vec<intvar>& st, vec<int>& du) {
  new disj_int(s, st, du);
}

void disjunctive_var(solver_data* s, vec<intvar>& st, vec<intvar>& du) {
  new disj_var(s, st, du);
}

}
