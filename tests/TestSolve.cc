#include <iostream>
#include <cstdio>
#include "solver/solver.h"
#include "solver/solver_data.h"
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

using namespace phage;

std::ostream& operator<<(std::ostream& o, const solver::result& r) {
  switch(r) {
    case solver::SAT:
      o << "SAT";
      break;
    case solver::UNSAT:
      o << "UNSAT";
      break;
    default:
      o << "UNKNOWN";
  }
  return o;
}
int main(int argc, char** argv) {
  solver s;

  intvar x = s.new_intvar(-10, 10);
  intvar y = s.new_intvar(-10, 10);
  intvar z = s.new_intvar(-10, 10);

  solver_data& sd(*s.data);

  add_clause(sd, x <= -5, y <= -5);
  add_clause(sd, x >= 5, y >= 5);
  add_clause(sd, x >= 0, z >= 0);
  add_clause(sd, z >= 0, y >= 0);
  
  solver::result r = s.solve();
  std::cout << "Result: " << r << std::endl;

  if(r == solver::SAT) {
    fprintf(stdout, "[x, y, z] ~> [%lld, %lld, %lld]\n", x.lb(), y.lb(), z.lb());
  }
}
