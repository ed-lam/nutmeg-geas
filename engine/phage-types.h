#ifndef PHAGE_TYPES__H
#define PHAGE_TYPES__H
#include <stdint.h>

namespace phage {

class lbool {
  lbool(int _x) : x(_x) { }
public:
  static lbool of_int(int x) { return lbool(x); }

  lbool(void) : x(0) { }
  lbool(bool b) : x(b ? 1 : -1) { }

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
    return patom_t(pid^1, pval_max - val - 1);
  }

  pid_t pid;
  pval_t val;
};

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

}
#endif
