#ifndef __PHAGE_BOOLVAR_H__
#define __PHAGE_BOOLVAR_H__
#include "engine/atom.h"
#include "engine/manager.h"

typedef int bvar_id;

class BoolVar;

// A Boolean atom is represented as
// id: (var_id|sign)
// val: 0

class BVarMan : public AtomManager {
public:
  BVarMan(env* _e)
    : AtomManager(_e)
  { }

  BoolVar newVar(void);

  lbool _value(bvar_id id) {
    return mk_lbool(assigns[id]);
  }

  lbool value(_atom x)
  {
    return _value(x.tok);
  }

  atom bvar_false(bvar_id id) {
    return mk_atom(tok_ids[id]<<1, 0);
  }

  atom bvar_true(bvar_id id)
  {
    return mk_atom(tok_ids[id]<<1|1, 0);
  }

  // Get a concrete lit for the corresponding
  // atom. May already exist.
  lit bind(_atom x) {
    bvar_id id(x.tok>>1);

    int v = binding[id];
    if(v == -1)
    {
      // Get a new concrete variable
      // from the env.
      v = e->new_catom(mk_atom(tok_ids[id], x.info));
      binding[id] = v;
    }

    return mk_lit(v, x.tok&1);
  }

  // Mark a atom as no longer persistent
  void unbind(_atom x) { }

  // Assert a atom
  bool post(_atom x, vec<atom>& out_confl)
  {
    bvar_id id(x.tok>>1); 
    int asg = 2*(x.tok&1) - 1;
    if(assigns[id] == -asg)
    {
      // Failure.
      atom l(from_atom_(x));
      out_confl.push(l);
      out_confl.push(~l);
      return false;
    }
    if(assigns[id] == 0)
      assigns[id] = asg;

    fprintf(stderr, "WARNING: Wake up clauses and propagators from BVarMan::post.\n");
    return true; 
  }

  // Can we do this more cheaply?
  // lit undo(_atom& x) { }

  // x -> y?
  bool le(_atom x, _atom y)
  {
    return x.tok == y.tok;
  }

  // Are all variables managed by this fixed?
  bool is_fixed(void) {
    // Dumb approach; fix this later.
    for(int vi = 0; vi < assigns.size(); vi++)
    {
      if(assigns[vi] == 0)
        return false;
    }
    return true;
  }

  // Choose a branch literal. Extend to handle
  // branches later.
  atom branch(void) {
    // Again, dumb approach.
    for(int vi = 0; vi < assigns.size(); vi++)
    {
      if(assigns[vi] == 0)
        return bvar_true(vi);
    }
    return atom_undef();
  }

  // Conflict clause resolution; atom_val is always zero.
  ResolvableT is_resolvable(atom_id id, atom_val val, atom_val prev) {
    return R_ResolveElim;
  }

  void collect(atom_id id, atom_val v, vec<atom>& learnt_out) {
    learnt_out.push(mk_atom(id, v));   
  };

protected:
  // Since I haven't impatomented sub-int trail eatoments,
  // we represent our assignments as ints.
  vec<TrInt> assigns;
  vec<int> binding;
};

class BoolVar {
public:
  BoolVar(BVarMan* _man, bvar_id _id)
    : man(_man), id(_id)
  { }

  lbool value(void) { return man->_value(id); }

  operator atom() {
    return man->bvar_true(id);
  }

protected:
  BVarMan* man; 
  bvar_id id;
};

#endif
