#ifndef __PHAGE_INTVAR_H__
#define __PHAGE_INTVAR_H__
#include "engine/atom.h"
#include "engine/base-types.h"
#include "engine/manager.h"
#include "engine/propagator.h"
#include "engine/trail.h"
#include "engine/env.h"
#include "engine/branch.h"
#include "vars/var-interface.h"

typedef int ivar_id;

class IntVar;

enum IManKind { IV_Eager, IV_Lazy };

enum IVarEvent { IVE_LB = 1, IVE_UB = 2, IVE_LU = 3, IVE_FIX = 4 };

class IVarManager : public AtomManager, public Brancher {
public:
  IVarManager(env* e)
    : AtomManager(e), Brancher(e)
  { }

  virtual IntVar newVar(int lb, int ub) = 0;

  virtual void add_watch(ivar_id id, WatcherT<char>* w,
    int ref, char events) = 0;

  virtual int lb(ivar_id id) = 0;
  virtual int ub(ivar_id id) = 0;
  virtual bool indom(ivar_id id, int k) = 0;

  virtual atom le_atom(ivar_id id, int k) = 0;
  virtual atom eq_atom(ivar_id id, int k) = 0;

  // Standard atom-manager operations.
//  virtual void attach(_atom& x, Watcher* w, int k) = 0;
//  virtual void detach(_atom& x) { }

//  virtual bool post(_atom& x, vec<atom>& out_confl) = 0;
//  virtual lbool value(_atom& x) = 0;
//  virtual bool le(_atom& x, _atom& y) = 0;

//  virtual bool is_fixed(void) = 0;
//  virtual atom branch(void) = 0;
//  virtual ResolvableT is_resolvable(atom_id id, atom_val val, atom_val prev) = 0;
//  virtual void collect(atom_id id, atom_val v, vec<atom>& learnt_out) = 0;
};

class IntVar : public NumVar<int, IntVar> {
public:
  IntVar(IVarManager* _man,  ivar_id _id)
    : man(_man), id(_id)
  { }

  atom le(int k) { return man->le_atom(id, k); }
  atom lt(int k) { return man->le_atom(id, k-1); }
  atom ge(int k) { return ~ man->le_atom(id, k-1); }
  atom gt(int k) { return ~ man->le_atom(id, k); }
  atom eq(int k) { return man->eq_atom(id, k); }
//  atom ne(int k) { return ~ man->eq_atom(id, k); }

  int lb(void) { return man->lb(id); }
  int ub(void) { return man->ub(id); }
  bool in_domain(int v) { return man->indom(id, v); }

  int value(void) { assert(lb() == ub()); return lb(); }

  void add_watch(WatcherT<char>* w, int ref, char events)
  {
    man->add_watch(id, w, ref, events);
  }

protected:
  IVarManager* man;
  ivar_id id;
};

IVarManager* newIVarMan(env* e, IManKind kind);
#endif
