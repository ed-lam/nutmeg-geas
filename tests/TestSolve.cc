#include <iostream>
#include <cstdio>
#include "engine/env.h"
#include "engine/trail.h"
#include "engine/solver.h"

#include "vars/boolvar.h"

int main(int argc, char** argv)
{
  env* e = new env;
  solver s(e);

  BVarMan bman(e);

  Trailed<int> i(&(e->gen_trail), 0);

  BoolVar x(bman.newVar());
  BoolVar y(bman.newVar());
  BoolVar z(bman.newVar());
  
  e->addClause(x, y, z);

  e->addClause(~x, ~y);
  e->addClause(~x, ~z);
  e->addClause(~y, ~z);
  e->addClause(~x, y);

  if(s.solve() == solver::SAT)
  {
    fprintf(stdout, "SAT\n");
  } else {
    fprintf(stdout, "UNSAT\n");
  }

  return 0;
}
