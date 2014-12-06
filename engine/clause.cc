#include "engine/env.h"
#include "engine/clause.h"

// Construct a clause from a set of atoms.
clause* _mk_clause(env* e, vec<atom>& ls, bool learnt)
{
  clause* cl = (clause*) malloc(sizeof(clause) + sizeof(lit)*(ls.size()));
  
  cl->sz = ls.size();
  cl->tags = 0;
  if(learnt)
    cl->tags |= Cl_Learnt;

  // For each atom, grab the corresponding
  // literal.
  for(int li = 0; li < ls.size(); li++) 
    cl->ls[li] = e->lit_of_atom(ls[li]);

  return cl;
}

// FIXME: Also need to handle initial selection of lits.
clause* mk_clause(env* e, vec<atom>& ls, bool learnt)
{
  return _mk_clause(e, ls, learnt);
}
