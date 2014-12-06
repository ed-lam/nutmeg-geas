#include <iostream>
#include <cstdio>
#include "engine/env.h"
#include "engine/trail.h"
#include "engine/solver.h"

#include "vars/boolvar.h"
#include "vars/intvar.h"

int main(int argc, char** argv)
{
  env* e = new env;
  solver s(e);

  BVarMan bman(e);

  Trailed<int> i(&(e->gen_trail), 0);

  BoolVar b(bman.newVar());
  BoolVar b2(bman.newVar());

  if(s.solve() == solver::SAT)
  {
    fprintf(stdout, "SAT\n");
  } else {
    fprintf(stdout, "UNSAT\n");
  }

  return 0;
}
