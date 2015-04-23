#include <iostream>
#include <cstdio>
#include "engine/env.h"
#include "engine/trail.h"
#include "engine/solver.h"

#include "vars/boolvar.h"
#include "vars/intvar.h"
#include "constraints/linear.h"

int main(int argc, char** argv)
{
  env* e = new env;
  solver s(e);

  BVarMan bman(e);
  IVarManager* iman(newIVarMan(e, IV_Lazy));

  IntVar x(iman->newVar(2, 10));
  IntVar y(iman->newVar(2, 10));
  IntVar z(iman->newVar(1, 10));

  vec<int> coeffs;
  vec<IntVar> xs;

  coeffs.push(1); coeffs.push(1); coeffs.push(-1);
  xs.push(x); xs.push(y); xs.push(z);

  new LinearLE<env,IntVar,int>(e, coeffs, xs, 1);

  coeffs[0] = -1; coeffs[1] = -1; coeffs[2] = 1;
  new LinearLE<env,IntVar,int>(e, coeffs, xs, -1);

  if(s.solve() == solver::SAT)
  {
    fprintf(stdout, "SAT\n");
    fprintf(stdout, "{x -> %d, y -> %d, z -> %d}\n",
      x.value(), y.value(), z.value());
  } else {
    fprintf(stdout, "UNSAT\n");
  }

  return 0;
}
