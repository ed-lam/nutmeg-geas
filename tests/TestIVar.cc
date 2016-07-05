#include <iostream>
#include <cstdio>

#include "solver/solver.h"

#if 0
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
  
  e->post(v.ge(5), expln());
  fprintf(stdout, "lb(v[>=5]) = %d\n", lb(v));

  if(s.solve() == solver::SAT)
  {
    fprintf(stdout, "SAT\n");
    fprintf(stdout, "{v -> %d}\n", v.value());
  } else {
    fprintf(stdout, "UNSAT\n");
  }

  return 0;
}
#endif

using namespace phage;

int main(int argc, char** argv) {
  solver s;

  intvar x = s.new_intvar(-10, 10);
  intvar y = s.new_intvar(-10, 10);

  solver_data& sd(*s.data);

  add_clause(sd, x <= -5, x >= 5);
  
  fprintf(stdout, "x: [%lld, %lld]\n", x.lb(), x.ub());
  fprintf(stdout, "y: [%lld, %lld]\n", y.lb(), y.ub());

  enqueue(sd, x >= 0, reason());
   
  if(!propagate(sd))
    ERROR;  

  fprintf(stdout, "x: [%lld, %lld]\n", x.lb(), x.ub());
  fprintf(stdout, "y: [%lld, %lld]\n", y.lb(), y.ub());
  return 0;
}
