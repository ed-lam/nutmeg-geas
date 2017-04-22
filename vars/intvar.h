#ifndef PHAGE_VAR__H
#define PHAGE_VAR__H
#include <unordered_map>

#include "utils/interval.h"
#include "engine/infer.h"
#include "solver/model.h"
#include "solver/solver_data.h"

namespace phage {

class intvar_manager;

enum intvar_event { E_None = 0, E_LB = 1, E_UB = 2, E_LU = 3, E_FIX = 4 };

class intvar {
  friend class intvar_manager;

  static const pval_t offset = ((pval_t) INT64_MIN); 
  // static const pval_t offset = ((pval_t) INT32_MIN); 

public:
#ifdef PVAL_32
  typedef int32_t val_t;
#else
  typedef int64_t val_t;
#endif

  static val_t to_int(pval_t v) { return (val_t) (offset + v); }
  static pval_t from_int(val_t v) { return ((pval_t) v) - offset; }

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

  val_t lb(const vec<pval_t>& ctx) const;
  val_t ub(const vec<pval_t>& ctx) const;

  val_t lb(void) const;
  val_t ub(void) const;
  bool is_fixed(void) const;

  val_t lb_prev(void) const;
  val_t ub_prev(void) const;

  val_t lb_0(void) const;
  val_t ub_0(void) const;

  bool set_lb(val_t min, reason r);
  bool set_ub(val_t max, reason r);

  void attach(intvar_event e, watch_callback c);

  // FIXME: Update to deal with sparse
  num_range_t<val_t> domain(void) const {
    return num_range(lb(), ub()+1);
  }

  val_t model_val(const model& m) const;

  patom_t operator>=(val_t v) { return patom_t(pid, from_int(v)); }
  patom_t operator>(val_t v) { return patom_t(pid, from_int(v+1)); }
  patom_t operator<=(val_t v) { return ~patom_t(pid, from_int(v+1)); }
  patom_t operator<(val_t v) { return ~patom_t(pid, from_int(v)); }
  patom_t operator==(val_t v);
  patom_t operator!=(val_t v);

  solver_data* s;
  intvar_manager* man;
  int idx;
  pid_t pid;
};

class intvar_manager {
public:
  typedef intvar::val_t val_t;

  enum ivar_kind { IV_EAGER, IV_SPARSE, IV_LAZY };

  struct eq_elt { val_t val; patom_t atom; };
  struct eq_info { pid_t pid; pval_t val; };

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
     
  intvar new_var(val_t lb, val_t ub);

  void attach(unsigned int vid, intvar_event e, watch_callback c);

  bool in_domain(unsigned int vid, val_t val);
  patom_t make_eqatom(unsigned int vid, val_t val);
  bool make_sparse(unsigned int vid, vec<val_t>& vals);
  void make_eager(unsigned int vid);

  vec<pid_t> var_preds;

  vec< vec<watch_callback> > lb_callbacks;
  vec< vec<watch_callback> > ub_callbacks;
  vec< vec<watch_callback> > fix_callbacks;

  // FIXME: Switch to a lighter-weight data-structure
  std::vector< std::unordered_map<pval_t, patom_t> > eqtable;
  vec<eq_info> eqinfo;

  solver_data* s;
};

// inline patom_t intvar_base::operator==(int64_t v) {
inline patom_t intvar::operator==(val_t v) {
  return man->make_eqatom(idx, v);
}

// inline patom_t intvar_base::operator!=(int64_t v) {
inline patom_t intvar::operator!=(val_t v) {
  return ~man->make_eqatom(idx, v);
}

inline bool in_domain(intvar x, int k) { return x.man->in_domain(x.idx, k); }

template<class T>
// bool intvar_base::make_sparse(vec<T>& vals) {
bool make_sparse(intvar x, vec<T>& vals) {
  vec<intvar::val_t> vs;
  for(const T& v : vals)
    vs.push((intvar::val_t) v);
  return x.man->make_sparse(x.idx, vs);
}

inline void make_eager(intvar x) { x.man->make_eager(x.idx); }

inline intvar::val_t to_int(pval_t v) { return intvar::to_int(v); }

inline pval_t from_int(intvar::val_t v) { return intvar::from_int(v); }


inline int_itv var_unsupp(intvar x) {
  return int_itv { x.ub_0()+1, x.lb_0()-1 };
}

inline int_itv var_range(intvar x) {
  return int_itv { x.lb(), x.ub() };
}

// forceinline
inline intvar::val_t intvar::lb(const vec<pval_t>& ctx) const {
  return to_int(ctx[pid]);
}
inline intvar::val_t intvar::ub(const vec<pval_t>& ctx) const {
  return to_int(pval_max - s->state.p_vals[pid^1]);
}

inline intvar::val_t intvar::lb(void) const {
  return to_int(s->state.p_vals[pid]);
}

// forceinline
inline intvar::val_t intvar::ub(void) const {
  return to_int(pval_max - s->state.p_vals[pid^1]);
}

/*
class intview {
public:
  // intvar_base(solver_data* _s, intvar_manager* _man, int idx, pid_t p);
  intview(intvar _x, int64_t _coef, int64_t _off)
    : x(_x), coef(_coef), off(_off) {
    assert(coef != 0);     
  }

  int64_t lb(void) const {
    return (coef < 0) ? coef*x.ub() + off : coef*x.lb() + off; 
  }
  int64_t ub(void) const {
    return (coef < 0) ? coef*x.lb() + off : coef*x.ub() + off;
  }
  bool is_fixed(void) const {
    return x.is_fixed();
  }

  int64_t lb_prev(void) const {
    return (coef < 0) ? coef*x.ub_prev() + off : coef*x.lb_prev() + off; 
  }
  int64_t ub_prev(void) const {
    return (coef < 0) ? coef*x.lb_prev() + off : coef*x.ub_prev() + off;
  }

  int64_t lb_0(void) const {
    return (coef < 0) ? coef*x.ub_0() + off : coef*x.lb_0() + off; 
  }

  int64_t ub_0(void) const {
    return (coef < 0) ? coef*x.lb_0() + off : coef*x.ub_0() + off;
  }

  bool set_lb(int64_t min, reason r) {
    NOT_YET;
    return true; 
  }
  bool set_ub(int64_t max, reason r) {
    NOT_YET;
    return true;
  }

  void attach(intvar_event e, watch_callback c) {
    // Switch events  
  }

  int64_t model_val(const model& m) const {
    return coef * x.model_val(m) + off;
  }

  // k x + c >= v ~~> x >= (v - c)/k
  patom_t operator>=(int64_t v) { 
    NOT_YET;
    return at_True;
  }
  patom_t operator>(int64_t v) {
    return (*this) >= v+1;
  }
  patom_t operator<=(int64_t v) {
    return ~((*this) > v);
  }
  patom_t operator<(int64_t v) {
    return ~((*this) >= v);
  }
  patom_t operator==(int64_t v) {
    if((v - off)%k == 0) {
      return (x == ((v - off)/k));
    } else {
      return at_False;
    }
  }

  patom_t operator!=(int64_t v) {
    return ~((*this) == v);
  }
  
  intvar x;
  int coef;
  int off;
};
*/

}
#endif
