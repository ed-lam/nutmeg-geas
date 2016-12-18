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
  propagator(solver_data* _s)
    : is_queued(false), s(_s) {
    queue_prop(); 
  }
  // Return the operator implementations
//  virtual prop_t get(void) = 0;

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

  bool is_queued;
protected:
  solver_data* s;
};

// Each propagator class should be an instance of this.
// And needs to define enum { is_idempotent = {true, false} };
template<class T>
class prop_inst {
  static inline T* cast(void* ptr) { return static_cast<T*>(ptr); }

  static bool propagate(void* ptr) { return cast(ptr)->propagate(); }
  static bool check_sat(void* ptr) { return cast(ptr)->check_sat(); }
  static void root_simplify(void* ptr) { return cast(ptr)->root_simplify(); }
  static void cleanup(void* ptr) { return cast(ptr)->cleanup(); }

public:
  prop_t get(void) {
    return prop_t { propagate, check_sat, root_simplify, cleanup, T::is_idempotent, this }; 
  }
};

typedef void (*expl_fun)(void*, int , pval_t, vec<clause_elt>&);

template<class T, class E>
struct exfun {
  static void explain(void* p, int data, pval_t val, 
    vec<clause_elt>& expl) {
    E(static_cast<T*>(p), data, val, expl);
  }
};

}
#endif
