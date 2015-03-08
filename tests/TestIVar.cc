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

//  std::cout << &(e->gen_vtrail) << std::endl;

  BVarMan bman(e);
  IVarManager* iman(newIVarMan(e, IV_Lazy));

  IntVar v(iman->newVar(0, 10));

  fprintf(stdout, "lb(v) = %d\n", lb(v));

  if(s.solve() == solver::SAT)
  {
    fprintf(stdout, "SAT\n");
  } else {
    fprintf(stdout, "UNSAT\n");
  }

  return 0;
}
