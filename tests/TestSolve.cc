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

  BoolVar b(bman.newVar());

  if(s.solve())
  {
    fprintf(stdout, "SAT\n");
  } else {
    fprintf(stdout, "UNSAT\n");
  }

  return 0;
}
