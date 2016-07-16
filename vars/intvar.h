#ifndef PHAGE_VAR__H
#define PHAGE_VAR__H

#include "engine/infer.h"
#include "solver/solver_data.h"

namespace phage {

class intvar_manager;

enum intvar_event { E_None = 0, E_LB = 1, E_UB = 2, E_LU = 3 };
/*
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
*/

class intvar_interface {
public:
  virtual int64_t lb(void) const = 0;
  virtual int64_t ub(void) const = 0;

  virtual bool set_lb(int64_t min, reason r) = 0;
  virtual bool set_ub(int64_t max, reason r) = 0;

  virtual void attach(intvar_event e, watch_callback call) = 0;

  virtual patom_t operator>=(int64_t v) = 0;
  virtual patom_t operator>(int64_t v) = 0;
  virtual patom_t operator<=(int64_t v) = 0;
  virtual patom_t operator<(int64_t v) = 0;
};

class intvar {
public:
  intvar(intvar_interface* _x)
    : x(_x) { } 

  intvar(void)
    : x(nullptr) { }

  int64_t lb(void) const { return x->lb(); }
  int64_t ub(void) const { return x->ub(); }

  void attach(intvar_event e, watch_callback c) { x->attach(e, c); }

  bool in_domain(int64_t k) { return x->lb() <= k && k <= x->ub(); }

  bool set_lb(int64_t min, reason r) { return x->set_lb(min, r); }
  bool set_ub(int64_t max, reason r) { return x->set_ub(max, r); }

  patom_t operator>=(int64_t v) { return (*x) >= v; }
  patom_t operator>(int64_t v) { return (*x) > v; }
  patom_t operator<=(int64_t v) { return (*x) <= v; }
  patom_t operator<(int64_t v) { return (*x) < v; }
protected:
  intvar_interface* x;
};

class intvar_base : public intvar_interface {
  friend class intvar_manager;

  static const pval_t offset = ((pval_t) INT64_MIN); 

public:
  static int64_t to_int(pval_t v) { return (int64_t) (offset + v); }
  static pval_t from_int(int64_t v) { return ((pval_t) v) - offset; }

  intvar_base(solver_data* _s, intvar_manager* _man, int idx, pid_t p);

  int64_t lb(void) const;
  int64_t ub(void) const;

  bool set_lb(int64_t min, reason r);
  bool set_ub(int64_t max, reason r);

  void attach(intvar_event e, watch_callback c);

  patom_t operator>=(int64_t v) { return patom_t(pid, from_int(v)); }
  patom_t operator>(int64_t v) { return patom_t(pid, from_int(v+1)); }
  patom_t operator<=(int64_t v) { return ~patom_t(pid, from_int(v+1)); }
  patom_t operator<(int64_t v) { return ~patom_t(pid, from_int(v)); }

  solver_data* s;
  intvar_manager* man;
  int idx;
  pid_t pid;
};

/*
class intvar_base : public intvar_interface {
  friend class intvar_manager;

  static const pval_t offset = ((pval_t) INT64_MIN); 

public:
  static int64_t to_int(pval_t v) { return (int64_t) (offset + v); }
  static pval_t from_int(int64_t v) { return ((pval_t) v) - offset; }

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
*/

class intvar_manager {
public:
  intvar_manager(solver_data* _s);
     
  intvar new_var(int64_t lb, int64_t ub);

  void attach(unsigned int vid, intvar_event e, watch_callback c);

  vec<pid_t> var_preds;

  vec< vec<watch_callback> > lb_callbacks;
  vec< vec<watch_callback> > ub_callbacks;

  solver_data* s;
};

}
#endif
