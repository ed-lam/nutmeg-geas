#include <libguile.h>
#include "scm_bind.h"

// #include "../engine/Solver.h"

//typedef SCM(*scm_t_subr)(void);

static scm_t_bits bvar_tag;
static scm_t_bits ivar_tag;
static scm_t_bits prop_tag;

static SCM scm_solver_status(void)
{
//  solver->printStatus();
  return SCM_UNSPECIFIED;
}

static SCM scm_getprop(SCM p)
{
  /*
  int pid(scm_to_int(p));
  Propagator* prop = solver->getProp(pid);
  SCM prop_smob;
  SCM_NEWSMOB(prop_smob, prop_tag, prop);
  return prop_smob;
  */
  return SCM_UNSPECIFIED;
}

SCM scm_newbool(SCM pos)
{
  /*
  Lit bv(Lit(solver->newVar(), 1));
  
  SCM bvar_smob;
  SCM_NEWSMOB(bvar_smob, bvar_tag, toInt(bv));
  return bvar_smob;
  */
  return SCM_UNSPECIFIED;
}

void init_scm_types(void)
{
  // No additional space necessary.
  // Just references/identifiers
  /*
  bvar_tag = scm_make_smob_type("boolvar", 0);
  ivar_tag = scm_make_smob_type("intvar", 0);
  prop_tag = scm_make_smob_type("propagator", 0);
  */
}

void scm_init_bindings(void)
{
  init_scm_types();
  /*
  scm_c_define_gsubr("status", 0, 0, 0, (scm_t_subr) scm_solver_status);
  scm_c_define_gsubr("get-prop", 1, 0, 0,  (scm_t_subr) scm_getprop);
  scm_c_define_gsubr("bool-var", 0, 0, 0,  (scm_t_subr) scm_newbool);
  */
}
