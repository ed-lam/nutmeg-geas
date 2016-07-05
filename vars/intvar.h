#ifndef PHAGE_VAR__H
#define PHAGE_VAR__H

#include "engine/infer.h"
#include "solver/solver_data.h"

namespace phage {

class intvar_manager;

class intvar {
  friend class intvar_manager;

  static const pval_t offset = ((pval_t) INT64_MIN); 

  static int64_t to_int(pval_t v) { return (int64_t) (offset + v); }
  static pval_t from_int(int64_t v) { return ((pval_t) v) - offset; }

public:
  intvar(solver_data* _s, pid_t p);

  int64_t lb(void) const;
  int64_t ub(void) const;

  bool set_lb(int64_t min, reason r);
  bool set_ub(int64_t max, reason r);

  patom_t operator>=(int64_t v) { return patom_t(pid, from_int(v)); }
  patom_t operator>(int64_t v) { return patom_t(pid, from_int(v+1)); }
  patom_t operator<=(int64_t v) { return ~patom_t(pid, from_int(v+1)); }
  patom_t operator<(int64_t v) { return ~patom_t(pid, from_int(v)); }

  solver_data* s;
  pid_t pid;
};

class intvar_callback {
public:
  enum Event { E_LB = 1, E_UB = 2, E_LU = 3 };
  typedef void (*fun)(void*, int, Event);
  
  intvar_callback(fun _f, void* _data, int _tag)
    : f(_f), data(_data), tag(_tag) { }

  void operator()(Event e) { f(data, tag, e); }
protected:
  fun f;
  void* data;
  int tag;
};

class intvar_manager {
public:
  intvar_manager(solver_data* _s);
     
  intvar new_var(int64_t lb, int64_t ub);

  vec<pid_t> var_preds;

  vec< vec<intvar_callback> > lb_callbacks;
  vec< vec<intvar_callback> > ub_callbacks;

  solver_data* s;
};

}
#endif
