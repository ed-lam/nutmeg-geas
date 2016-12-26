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

struct brancher_s;
typedef struct brancher_s* brancher;

typedef struct {
  int conflicts;
  int restarts;
} stats;

solver new_solver(void);
void destroy_solver(solver);

intvar new_intvar(solver, int lb, int ub);
void destroy_intvar(intvar);

atom new_boolvar(solver);

typedef enum { VAR_INORDER, VAR_FIRSTFAIL, VAR_LEAST, VAR_GREATEST } var_choice;
typedef enum { VAL_MIN, VAL_MAX, VAL_SPLIT } val_choice;

brancher new_brancher(var_choice, val_choice, intvar*, int);
brancher seq_brancher(brancher*, int);
void add_brancher(solver, brancher);

result solve(solver, int);

int post_atom(solver, atom);
int post_clause(solver, atom*, int);

model get_model(solver);
void destroy_model(model);

int int_value(model, intvar);
int atom_value(model, atom);

atom ivar_le(intvar, int);
atom ivar_eq(intvar, int);

pred_t new_pred(solver, int, int);
atom pred_ge(pred_t, int);

stats get_statistics(solver);

#ifdef __cplusplus
}
#endif

#endif
