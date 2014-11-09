#ifndef __PHAGE_BOOLVAR_H__
#define __PHAGE_BOOLVAR_H__
#include "engine/lemma.h"
#include "engine/manager.h"

typedef int bvar_id;

class BoolVar;

// A Boolean lemma is represented as
// id: var_id
// val: {0, 1}

class BVarMan : public LemmaManager {
public:
  BVarMan(env* _e)
    : LemmaManager(_e)
  { }

  BoolVar newVar(void);

  lbool value(bvar_id id) {
    assert (0 && "BVarMan::value not yet implemented.");
    return l_Undef;
  }

  lemma bvar_true(bvar_id id) {
    return mk_lem(kind, id<<1, 0);  
  }

  lemma bvar_false(bvar_id id)
  {
    return ~bvar_true(id);
  }

  // Get a concrete lit for the corresponding
  // lemma. May already exist.
  lit bind(_lemma& x) {
    assert (0 && "BVarMan::bind not yet implemented.");
    return mk_lit(-1, 0);
  }

  // Mark a lemma as no longer persistent
  void unbind(_lemma& x) { }

  // Assert a lemma
  bool post(_lemma& x, vec<lemma>& out_confl)
  {
    assert(0 && "BVarMan::post not yet implemented.");
    return true; 
  }
  // Can we do this more cheaply?
  // lit undo(_lemma& x) { }

  // x -> y?
  bool le(_lemma& x, _lemma& y)
  {
    return x.id == y.id;
  }

  // Are all variables managed by this fixed?
  bool is_fixed(void) {
    assert (0 && "is_fixed not yet implemented.");
  }

  // Choose a branch literal. Extend to handle
  // branches later.
  _lemma branch(void) {
    assert(0 && "Branching not yet implemented.");
  }

  // Conflict clause resolution; lem_val is always zero.
  ResolvableT is_resolvable(lem_id id, lem_val val, lem_val prev) {
    return R_ResolveElim;
  }

  void collect(lem_id id, lem_val v, vec<lemma>& learnt_out) {
    learnt_out.push(mk_lem(kind, id, v));   
  };
};

class BoolVar {
public:
  BoolVar(BVarMan* _man, bvar_id _id)
    : man(_man), id(_id)
  { }

  lbool value(void) { return man->value(id); }
  operator lemma() {
    return man->bvar_true(id);
  }

protected:
  BVarMan* man; 
  bvar_id id;
};

#endif
