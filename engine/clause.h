#ifndef __PHAGE_CLAUSE_H__
#define __PHAGE_CLAUSE_H__

#include "mtl/Vec.h"
#include "engine/sat.h"

enum ClauseTags { Cl_Learnt = 1 };

typedef struct {
  int sz;
  int tags;
  lit ls[0];  
} clause;

#include "engine/atom.h"
#include "engine/env.h"

clause* mk_clause(env* e, vec<atom>& ls);
#endif
