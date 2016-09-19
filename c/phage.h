#ifndef PHAGE_H
#define PHAGE_H
// Top-level C interface
#include "c/atom.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef enum { SAT, UNSAT, UNKNOWN } result;

struct solver_s;
typedef struct solver_s* solver;

struct intvar_s;
typedef struct intvar_s* intvar;

struct model_s;
typedef struct model_s* model;

solver new_solver(void);
void destroy_solver(solver);

intvar new_intvar(solver, int lb, int ub);
void destroy_intvar(intvar);

atom new_boolvar(solver);

result solve(solver, int);

int post_atom(solver, atom);
int post_clause(solver, atom*, int);

model get_model(solver);
void destroy_model(model);

int int_value(model, intvar);
int atom_value(model, atom);

atom ivar_le(intvar, int);
atom ivar_eq(intvar, int);

#ifdef __cplusplus
}
#endif

#endif
