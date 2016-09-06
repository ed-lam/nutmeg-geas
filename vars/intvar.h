#ifndef PHAGE_VAR__H
#define PHAGE_VAR__H
#include <unordered_map>

#include "utils/interval.h"
#include "engine/infer.h"
#include "solver/model.h"
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

// GKG: Perhaps refactor to avoid the virtual method
// calls.
/*
class intvar_interface {
public:
  virtual int64_t lb(void) const = 0;
  virtual int64_t ub(void) const = 0;

  // bounds at previous decision level
  virtual int64_t lb_prev(void) const = 0;
  virtual int64_t ub_prev(void) const = 0;

  // bounds at root level
  virtual int64_t lb_0(void) const = 0;
  virtual int64_t ub_0(void) const = 0;

  virtual bool set_lb(int64_t min, reason r) = 0;
  virtual bool set_ub(int64_t max, reason r) = 0;

  virtual void attach(intvar_event e, watch_callback call) = 0;

  virtual int64_t model_val(const model& m) const = 0;
  
  virtual patom_t operator>=(int64_t v) = 0;
  virtual patom_t operator>(int64_t v) = 0;
  virtual patom_t operator<=(int64_t v) = 0;
  virtual patom_t operator<(int64_t v) = 0;
  virtual patom_t operator==(int64_t v) = 0;
  virtual patom_t operator!=(int64_t v) = 0;
};

class intvar {
public:
  typedef int64_t val_t;

  intvar(intvar_interface* _x)
    : x(_x) { } 

  intvar(void)
    : x(nullptr) { }

  int64_t lb(void) const { return x->lb(); }
  int64_t ub(void) const { return x->ub(); }

  int64_t lb_prev(void) const { return x->lb_prev(); }
  int64_t ub_prev(void) const { return x->ub_prev(); }

  int64_t lb_0(void) const { return x->lb_0(); }
  int64_t ub_0(void) const { return x->ub_0(); }

  void attach(intvar_event e, watch_callback c) { x->attach(e, c); }

  bool in_domain(int64_t k) { return x->lb() <= k && k <= x->ub(); }

  bool set_lb(int64_t min, reason r) { return x->set_lb(min, r); }
  bool set_ub(int64_t max, reason r) { return x->set_ub(max, r); }

  int64_t model_val(model& m) const { return x->model_val(m); }

  patom_t operator>=(int64_t v) { return (*x) >= v; }
  patom_t operator>(int64_t v) { return (*x) > v; }
  patom_t operator<=(int64_t v) { return (*x) <= v; }
  patom_t operator<(int64_t v) { return (*x) < v; }
  patom_t operator==(int64_t v) { return (*x) == v; }
  patom_t operator!=(int64_t v) { return (*x) != v; }

  num_range_t<int64_t> domain(void) const {
    return num_range(lb(), ub()+1);
  }
protected:
  intvar_interface* x;
};
*/

// class intvar_base : public intvar_interface {
class intvar {
  friend class intvar_manager;

  static const pval_t offset = ((pval_t) INT64_MIN); 

public:
  typedef int64_t val_t;

  static int64_t to_int(pval_t v) { return (int64_t) (offset + v); }
  static pval_t from_int(int64_t v) { return ((pval_t) v) - offset; }

  // intvar_base(solver_data* _s, intvar_manager* _man, int idx, pid_t p);
  intvar(solver_data* _s, intvar_manager* _man, int idx, pid_t p);
  intvar(void)
    : s(nullptr), man(nullptr), idx(0), pid(0) { }

  intvar(const intvar& o)
    : s(o.s), man(o.man), idx(o.idx), pid(o.pid) { }

  intvar& operator=(const intvar& o) {
    s = o.s;
    man = o.man;
    idx = o.idx;
    pid = o.pid;
    return *this;
  }

  int64_t lb(void) const;
  int64_t ub(void) const;
  bool is_fixed(void) const;

  int64_t lb_prev(void) const;
  int64_t ub_prev(void) const;

  int64_t lb_0(void) const;
  int64_t ub_0(void) const;

  bool set_lb(int64_t min, reason r);
  bool set_ub(int64_t max, reason r);

  void attach(intvar_event e, watch_callback c);

  // FIXME: Update to deal with sparse
  num_range_t<int64_t> domain(void) const {
    return num_range(lb(), ub()+1);
  }

  int64_t model_val(const model& m) const;

  patom_t operator>=(int64_t v) { return patom_t(pid, from_int(v)); }
  patom_t operator>(int64_t v) { return patom_t(pid, from_int(v+1)); }
  patom_t operator<=(int64_t v) { return ~patom_t(pid, from_int(v+1)); }
  patom_t operator<(int64_t v) { return ~patom_t(pid, from_int(v)); }
  patom_t operator==(int64_t v);
  patom_t operator!=(int64_t v);

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
  enum ivar_kind { IV_EAGER, IV_SPARSE, IV_LAZY };

  struct eq_elt { int64_t val; patom_t atom; };

  class var_data {
  public: 
    ivar_kind kind;
    pid_t pred;
     
    // In the eager case, it's just an array [with an offset]
    // In the sparse and lazy case, they're
    // hash tables.
    int base;
    eq_elt* elts;
    size_t elts_maxsz;
    size_t elts_count;
  };

  intvar_manager(solver_data* _s);
     
  intvar new_var(int64_t lb, int64_t ub);

  void attach(unsigned int vid, intvar_event e, watch_callback c);

  bool in_domain(unsigned int vid, int64_t val);
  patom_t make_eqatom(unsigned int vid, int64_t val);
  bool make_sparse(unsigned int vid, vec<int64_t>& vals);

  vec<pid_t> var_preds;

  vec< vec<watch_callback> > lb_callbacks;
  vec< vec<watch_callback> > ub_callbacks;

  // FIXME: Switch to a lighter-weight data-structure
  std::vector< std::unordered_map<pval_t, patom_t> > eqtable;

  solver_data* s;
};

// inline patom_t intvar_base::operator==(int64_t v) {
inline patom_t intvar::operator==(int64_t v) {
  return man->make_eqatom(idx, v);
}

// inline patom_t intvar_base::operator!=(int64_t v) {
inline patom_t intvar::operator!=(int64_t v) {
  return ~man->make_eqatom(idx, v);
}

template<class T>
// bool intvar_base::make_sparse(vec<T>& vals) {
bool make_sparse(intvar x, vec<T>& vals) {
  vec<int64_t> vs;
  for(const T& v : vals)
    vs.push((int64_t) v);
  return x.man->make_sparse(x.idx, vs);
}

inline int64_t to_int(pval_t v) { return intvar::to_int(v); }

inline pval_t from_int(int64_t v) { return intvar::from_int(v); }


inline int_itv var_unsupp(intvar x) {
  return int_itv { x.ub_0()+1, x.lb_0()-1 };
}

inline int_itv var_range(intvar x) {
  return int_itv { x.lb(), x.ub() };
}


}
#endif
