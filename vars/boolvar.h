#ifndef __PHAGE_BOOLVAR_H__
#define __PHAGE_BOOLVAR_H__
#include <cstdio>
#include "engine/atom.h"
#include "engine/manager.h"
#include "engine/branch.h"

typedef int bvar_id;

class BoolVar;

// A Boolean atom is represented as
// id: (var_id|sign)
// val: 0

class BVarMan : public AtomManager, public Brancher {
public:
  BVarMan(env* _e)
    : AtomManager(_e), Brancher(_e)
  { }

  bvar_id tok_var(atom_tok tok) { return tok>>1; }
  bool tok_sign(atom_tok tok) { return tok&1; }

  BoolVar newVar(void);

  lbool _value(bvar_id id) {
    return mk_lbool(assigns[id]);
  }

  lbool value(_atom x)
  {
    lbool val = _value(tok_var(x.tok));
    return tok_sign(x.tok) ? val : ~val;
  }

  int false_level(_atom x)
  {
    assert(value(x) == l_False);
    return level[tok_var(x.tok)];
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
  void attach(_atom x, Watcher* w, int k) {
    ws[x.tok].push(Watcher::Info(w, k));
  }

  // Mark a atom as no longer persistent
  void detach(_atom x) {
    ws[x.tok].clear();
  }

  // Assert a atom
  bool post(_atom x)
  {
    bvar_id id(x.tok>>1); 
    int asg = 2*(x.tok&1) - 1;
    if(assigns[id] == -asg)
    {
      return false;
    }
    if(assigns[id] == 0)
    {
      assigns[id] = asg;
      level[id] = e->level();
    }

    fprintf(stdout, "Waking %d watchers for %sb%d\n", ws[x.tok].size(), x.tok&1 ? "" : "-", id);

    // Call watchers for the literal
    for(Watcher::Info& w : ws[x.tok])
      w();

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
  vec<int> level;
  vec< vec<Watcher::Info> > ws;
};

class BoolVar {
public:
  BoolVar(BVarMan* _man, bvar_id _id)
    : man(_man), id(_id)
  { }

  lbool value(void) { return man->_value(id); }

  operator atom() const {
    return man->bvar_true(id);
  }

protected:
//  vec< vec<Watcher::Info> > watchers;

  BVarMan* man; 
  bvar_id id;
};

#endif
