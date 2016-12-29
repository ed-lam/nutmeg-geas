#ifndef PHAGE_PROPAGATOR__H
#define PHAGE_PROPAGATOR__H
#include "engine/infer-types.h"

namespace phage {
class solver_data;

// Lifting actual function pointers to avoid
// vtable lookups
struct prop_t {
  bool (*propagate)(void* p, vec<clause_elt>& confl);
  bool (*check_sat)(void* p);
  void (*root_simplify)(void* p);
  void (*cleanup)(void* p);

  bool is_idempotent;

  void* ptr;
};

class propagator {
public: 
  // Return the operator implementations
//  virtual prop_t get(void) = 0;

  propagator(solver_data* _s);

  virtual ~propagator(void) { }

  virtual bool propagate(vec<clause_elt>& confl) = 0;
  virtual bool check_sat(void) { return true; }
  virtual void root_simplify(void) { }
  virtual void cleanup(void) { is_queued = false; }
  
  // execute dispatches between the checker (in a
  // half-reified case) and proapagator (when it's
  // active).
  // FIXME: Not yet implemented
  bool execute(vec<clause_elt>& confl);

  void queue_prop(void);

  bool is_idempotent;
  bool is_queued;
#ifdef PROOF_LOG
  int cons_id;
#endif
protected:
  solver_data* s;
};

// Each propagator class should be an instance of this.
// And needs to define enum { is_idempotent = {true, false} };
typedef void (*expl_fun)(void*, int , pval_t, vec<clause_elt>&);

template<class T>
class prop_inst {
  static inline T* cast(void* ptr) { return static_cast<T*>(ptr); }

public:
  static bool propagate(void* ptr) { return cast(ptr)->propagate(); }
  static bool check_sat(void* ptr) { return cast(ptr)->check_sat(); }
  static void root_simplify(void* ptr) { return cast(ptr)->root_simplify(); }
  static void cleanup(void* ptr) { return cast(ptr)->cleanup(); }

  static void wake_default(void* ptr, int dummy) { return cast(ptr)->queue_prop(); }
  
  // FIXME: Provide a central definition to_int
  template<void (*F)(T* ptr, int x, vec<clause_elt>& elt)>
  static void ex_nil(void* ptr, int x, pval_t pval, vec<clause_elt>& elt) {
    F(cast(ptr), x, elt);
  }

  template<void (*F)(T* ptr, int x, int64_t val, vec<clause_elt>& elt)>
  static void ex_lb(void* ptr, int x, pval_t pval, vec<clause_elt>& elt) {
    pval_t offset = ((pval_t) INT64_MIN); 
    F(cast(ptr), x, (int64_t) (offset + pval), elt);
  }

  template<void (*F)(T* ptr, int x, int64_t val, vec<clause_elt>& elt)>
  static void ex_ub(void* ptr, int x, pval_t pval, vec<clause_elt>& elt) {
    pval_t offset = ((pval_t) INT64_MIN); 
    F(cast(ptr), x, (int64_t) (offset + (pval_max - pval)), elt);
  }

  expl_thunk ex_thunk(expl_fun f, int x, char flags = 0) {
    return expl_thunk { f, this, x, flags };
  }

  prop_t get(void) {
    return prop_t { propagate, check_sat, root_simplify, cleanup, T::is_idempotent, this }; 
  }
};

/*
template<class T, class E>
struct exfun {
  static void explain(void* p, int data, pval_t val, 
    vec<clause_elt>& expl) {
    E(static_cast<T*>(p), data, val, expl);
  }
};
*/

}
#endif
