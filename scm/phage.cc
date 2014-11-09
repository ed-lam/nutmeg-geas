#include <libguile.h>
#include "../engine/solver.h"
#include "scm_bind.h"

int main(int argc, char** argv)
{
  env e;
  solver S(&e);
//  solver = &S;

  scm_init_guile();
  scm_init_bindings();  
  scm_shell(argc, argv);
  return 0;
}
