#include <iostream>
#include <cstdio>
#if 0
#include "engine/env.h"
#include "engine/trail.h"
#include "engine/solver.h"

#include "vars/boolvar.h"

static const char* lbool_str[] = { "0", "?", "1" };

int main(int argc, char** argv)
{
  env* e = new env;
  solver s(e);

#if 0
  BVarMan bman(e);

  Trailed<int> i(&(e->gen_trail), 0);

  BoolVar var_x(bman.newVar());
  BoolVar var_y(bman.newVar());

  atom x(var_x);
  atom y(var_y);
//  BoolVar z(bman.newVar());
  
  /*
  e->addClause(x, y, z);

  e->addClause(~x, ~y);
  e->addClause(~x, ~z);
  e->addClause(~y, ~z);
  e->addClause(~x, y);
  */
  e->addClause(x, y);
  e->addClause(~x, y);
  e->addClause(~x, ~y);
//  e->addClause(~x, ~y);

  if(s.solve() == solver::SAT)
  {
    fprintf(stdout, "SAT:");
    printf("x -> %s, y -> %s\n",
      lbool_str[1+var_x.value().v],
      lbool_str[1+var_x.value().v]);
  } else {
    fprintf(stdout, "UNSAT\n");
  }
#endif

  return 0;
}
#endif

int main(int argc, char** argv) {

}
