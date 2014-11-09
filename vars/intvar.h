#ifndef __PHAGE_INTVAR_H__
#define __PHAGE_INTVAR_H__
#include "engine/lemma.h"
#include "engine/manager.h"

typedef int ivar_id;

class IntVar;

class IVarManager : public LemmaManager {
public:
  virtual IntVar newVar(int lb, int ub) = 0;

  virtual int lb(ivar_id id) = 0;
  virtual int ub(ivar_id id) = 0;
  virtual bool indom(ivar_id id, int k) = 0;

  virtual lemma le_lit(ivar_id id, int k) = 0;
  virtual lemma eq_lit(ivar_id id, int k) = 0;
};

class IntVar {
public:
  IntVar(IVarManager* _man,  ivar_id _id)
    : man(_man), id(_id)
  { }

  lemma le(int k) { return man->le_lit(id, k); }
  lemma lt(int k) { return man->le_lit(id, k-1); }
  lemma ge(int k) { return ~ man->le_lit(id, k-1); }
  lemma gt(int k) { return ~ man->le_lit(id, k); }
  lemma eq(int k) { return man->eq_lit(id, k); }
  lemma ne(int k) { return ~ man->eq_lit(id, k); }

  lemma lb(void) { return man->lb(id); }
protected:
  IVarManager* man;
  ivar_id id;
};

#endif
