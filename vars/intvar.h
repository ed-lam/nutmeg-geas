#ifndef __PHAGE_INTVAR_H__
#define __PHAGE_INTVAR_H__
#include "engine/atom.h"
#include "engine/manager.h"
#include "engine/propagator.h"
#include "engine/vTrail.h"
#include "engine/env.h"

typedef int ivar_id;

class IntVar;

enum IManKind { IV_Eager, IV_Lazy };

enum IVarEvent { IVE_LB = 1, IVE_UB = 2, IVE_LU = 3, IVE_FIX = 4 };

class IVarManager : public AtomManager {
public:
  IVarManager(env* e)
    : AtomManager(e)
  { }

  virtual IntVar newVar(int lb, int ub) = 0;

  virtual void add_watch(ivar_id id, int events,
    Propagator* p, int ref);

  virtual int lb(ivar_id id) = 0;
  virtual int ub(ivar_id id) = 0;
  virtual bool indom(ivar_id id, int k) = 0;

  virtual atom le_atom(ivar_id id, int k) = 0;
  virtual atom eq_atom(ivar_id id, int k) = 0;
};

class IntVar {
public:
  IntVar(IVarManager* _man,  ivar_id _id)
    : man(_man), id(_id)
  { }

  atom le(int k) { return man->le_atom(id, k); }
  atom lt(int k) { return man->le_atom(id, k-1); }
  atom ge(int k) { return ~ man->le_atom(id, k-1); }
  atom gt(int k) { return ~ man->le_atom(id, k); }
  atom eq(int k) { return man->eq_atom(id, k); }
  atom ne(int k) { return ~ man->eq_atom(id, k); }

  int lb(void) { return man->lb(id); }
  int ub(void) { return man->ub(id); }
  bool indom(int v) { return man->indom(id, v); }
protected:
  IVarManager* man;
  ivar_id id;
};

IVarManager* newIVarMan(env* e, IManKind& kind);
#endif
