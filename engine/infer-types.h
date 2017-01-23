#ifndef PHAGE_INFER_TYPES__H
#define PHAGE_INFER_TYPES__H
/* Types for the inference engine */
#include <stdint.h>
#include <vector>
#include "mtl/Vec.h"
#include "mtl/int-triemap.h"

#include "utils/defs.h"
#include "engine/phage-types.h"

namespace phage {

class watch_node;

class clause_elt {
public:
  clause_elt(patom_t _at)
    : atom(_at)
#ifdef CACHE_WATCH
    , watch(nullptr)
#endif
  { }
#ifdef CACHE_WATCH
  clause_elt(patom_t _at, watch_node* _watch)
    : atom(_at), watch(_watch)
  { }
#endif

  patom_t atom;
  // We cache the appropriate watch-list
#ifdef CACHE_WATCH
  watch_node* watch;
#endif
};

struct clause_extra {
  clause_extra(void)
    : depth(0), one_watch(0), is_learnt(0), act(0) { }
//  bool is_learnt;
//  int depth;
  int depth : 30;
  unsigned one_watch : 1;
  unsigned is_learnt : 1;

  double act;
#ifdef PROOF_LOG
  int ident;
#endif
};

class clause {
public:
  // Empty constructor, for temporary explanations
  clause(void) : extra(), sz(0) { }

  // As usual, don't use this directly...
  template<class T> clause(T& elts) {
    sz = 0;
    for(clause_elt e : elts)
      data[sz++] = e;
  }
  
  int size(void) const { return sz; }
  
  clause_elt& operator[](int ii) { return data[ii]; }
  clause_elt* begin(void) { return &(data[0]); }
  clause_elt* end(void) { return &(data[sz]); }
  
  range_t<clause_elt> tail(void) { return range(&data[1], &data[sz]); }

  clause_extra extra;

  int sz;
protected:
  clause_elt data[0];
};

// Use this instead
template<class T>
clause* clause_new(T& elts) {
  void* mem = malloc(sizeof(clause) + sizeof(clause_elt)*elts.size());
  return new (mem) clause(elts);
}

inline clause* alloc_clause_mem(int sz) {
  void* mem = malloc(sizeof(clause) + sizeof(clause_elt)*sz);
  clause* c = new (mem) clause();
  c->sz = sz;
  return c;
}

template<typename... Es>
clause* make_clause(clause_elt e, Es... rest) {
  vec<clause_elt> v;
  v.push(e);
  vec_push(v, rest...);
  return clause_new(v);
}

// If c == NULL, the clause is binary -- e0 is the 'other' literal
class clause_head {
public: 
  clause_head(patom_t _e0)
    : e0(_e0), c(nullptr) { }
  clause_head(patom_t _e0, clause* _c)
    : e0(_e0), c(_c) { }

  patom_t e0; // We can stop if e0 is true.
  clause* c;
};

struct watch_extra {
  watch_extra(void)
    : act(0), refs(0) { }

  double act;
  int refs;
};

// Watches for a given atom.
// Maintains a pointer to the next watch.
class watch_node {
public:
  watch_node(void)
    : succ(nullptr) { }
  // patom_t atom;
#ifdef DEBUG_WMAP
  pval_t curr_val;
#endif
  pval_t succ_val;
  watch_extra extra;
  watch_node* succ;  
  vec<clause_head> ws;
  vec<watch_callback> callbacks;
};

// For a given pid_t, map values to the corresponding
// watches.
// typedef std::map<pval_t, watch_node*> watch_map;
typedef uint64_triemap<uint64_t, watch_node*, UIntOps> watch_map;

// One of: a clause, a an atom, or a thunk

struct expl_thunk {
  enum expl_flags { Ex_BTPRED = 1, Ex_BTGEN = 2 };
  typedef void (*fun)(void*, int, pval_t, vec<clause_elt>&); 
  
  void operator()(pval_t val, vec<clause_elt>& ex) {
    f(ptr, data, val, ex);
  }

  template<class T, class F>
  void explain(void* ptr, int d, pval_t v, vec<clause_elt>& elt) {
    return F(static_cast<T*>(ptr), d, v, elt);
  }

  fun f;
  void* ptr;
  int data;

  char flags; // pack flags in ptr?
};

class reason {
  struct le_info { pid_t p; pval_t offset; };
public:
  enum RKind { R_Clause = 0, R_Atom = 1, R_Thunk = 2, R_LE = 3, R_NIL = 4 };

  reason(void)
    : kind(R_NIL) { }

  reason(patom_t _at)
    : kind(R_Atom), at(_at) { }

  reason(clause* _cl)
    : kind(R_Clause), cl(_cl) { }

  reason(expl_thunk t)
    : kind(R_Thunk), eth(t) { }

  reason(pid_t p, pval_t offset)
    : kind(R_LE), le({p, offset}) { }

  RKind kind; 
  union {
    patom_t at; 
    clause* cl;
    le_info le;
    /* Deal with thunk. */
    expl_thunk eth;
  };
#ifdef PROOF_LOG
  int origin;
#endif
};

// For late initialization of a predicate
class pred_init {
public:
  static void expl_none(void* ptr, int xi, pval_t p, vec<clause_elt>& ex) {
    return;
  }

  typedef pval_t (*fun)(void*, int, vec<pval_t>&);

  pred_init(fun _f, void* _obj, int _data, expl_thunk _eth)
    : f(_f), obj(_obj), data(_data), eth(_eth)
  { }
  pred_init(void)
    : f(nullptr), obj(nullptr), data(0),
      eth(expl_thunk { expl_none, nullptr, 0 }) { }
  
  pval_t operator()(vec<pval_t>& state) {
    assert(f);
    return f(obj, data, state);
  }

  reason expl(void) const { return eth; }

  operator bool() const { return f; }

protected:
  fun f;
  void* obj;
  int data;

  expl_thunk eth;
};

struct pinit_data { pid_t pi; pred_init init; };


}

#endif
