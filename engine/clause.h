#ifndef __PHAGE_CLAUSE_H__
#define __PHAGE_CLAUSE_H__

#include "mtl/Vec.h"
#include "engine/lemma.h"

typedef struct {
  int sz;
  int tags;
  lemma ls[0];  
} clause;

#include "engine/env.h"

clause* _mk_clause(vec<lemma>& ls);
clause* mk_clause(env* e, vec<lemma>& ls);
#endif
