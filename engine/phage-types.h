#ifndef PHAGE_TYPES__H
#define PHAGE_TYPES__H
#include <stdint.h>
#include "mtl/Vec.h"

namespace phage {

class lbool {
  lbool(int _x) : x(_x) { }
public:
  static lbool of_int(int x) { return lbool(x); }

  lbool(void) : x(0) { }
  lbool(bool b) : x(b ? 1 : -1) { }

  lbool operator==(const lbool& o) const { return x == o.x; }
  lbool operator!=(const lbool& o) const { return x != o.x; }
  lbool operator^(bool b) const { return lbool(b ? -x : x); }
  lbool operator~(void) const { return lbool(-x); }
  int to_int(void) const { return x; }

  char x;
};

static const lbool l_False = lbool::of_int(-1);
static const lbool l_Undef = lbool::of_int(0);
static const lbool l_True = lbool::of_int(1);

// Atomic predicate values are mapped onto [0, UINT64_MAX-1]
// However, atoms can range from [0, UINT64_MAX].
// Otherwise, ~[|x >= 0|] is not representable.
typedef uint64_t pval_t;
static const pval_t pval_max = UINT64_MAX-1;
static const pval_t pval_err = UINT64_MAX;

typedef uint32_t pid_t;

class patom_t {
public:
  patom_t(void) : pid(UINT32_MAX), val(0) { }

  patom_t(pid_t _pid, pval_t _val) : pid(_pid), val(_val) { }

  bool operator==(const patom_t& o) const {
    return pid == o.pid && val == o.val;
  }
  bool operator!=(const patom_t& o) const {
    return pid != o.pid || val != o.val;
  }

  patom_t operator~(void) const {
    return patom_t(pid^1, pval_max - val + 1);
  }

  pid_t pid;
  pval_t val;
};

static const pid_t pid_None = UINT32_MAX;
static const patom_t at_Undef = patom_t(UINT32_MAX, 0);
static const patom_t at_Error = patom_t(UINT32_MAX, pval_max);

inline patom_t ge_atom(pid_t p, pval_t v) { return patom_t(p, v); }
inline patom_t le_atom(pid_t p, pval_t v) { return ~patom_t(p, v+1); }

// Event callbacks
class watch_callback {
public:
  typedef void (*fun)(void*, int);

  watch_callback(fun _f, void* _obj, int _data)
    : f(_f), obj(_obj), data(_data)
  { }

  void operator()(void) { f(obj, data); }
protected:
  fun f;
  void* obj;
  int data;
};

// For late initialization of a predicate
class pred_init {
public:
  struct prange_t {
    pval_t& operator[](int i) { return v[i]; }
    pval_t v[2];
  };
  typedef prange_t (*fun)(void*, int, vec<pval_t>&);

  pred_init(fun _f, void* _obj, int _data)
    : f(_f), obj(_obj), data(_data)
  { }
  pred_init(void)
    : f(nullptr), obj(nullptr), data(0) { }
  
  prange_t operator()(vec<pval_t>& state) {
    assert(f);
    return f(obj, data, state);
  }

  operator bool() const { return f; } 

protected:
  fun f;
  void* obj;
  int data;
};
struct pinit_data { pid_t pi; pred_init init; };

}
#endif
