#ifndef PHAGE_H
#define PHAGE_H
// Top-level C interface
#include "c/atom.h"
#include "solver/stats.h"
#include "solver/options.h"

#ifdef __cplusplus
#include <cstdio>
extern "C" {
#else
#include <stdio.h>
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

/*
typedef struct {
  int solutions;
  int conflicts;
  int restarts;
} stats;

// Urgh. Should just have stats and options as straight structs.
typedef struct {
  int learnt_dbmax;
  double learnt_growthrate;
  
  double pred_act_inc;
  double pred_act_decay;

  double learnt_act_inc;
  double learnt_act_decay;

  int restart_limit;
  double restart_growthrate;
} options;
*/

options default_opts(void);
solver new_solver(options opts);
void destroy_solver(solver);

intvar new_intvar(solver, int lb, int ub);
void destroy_intvar(intvar);
int make_sparse(intvar, int* vals, int sz);

atom new_boolvar(solver);

typedef enum { VAR_INORDER, VAR_FIRSTFAIL, VAR_LEAST, VAR_GREATEST } var_choice;
typedef enum { VAL_MIN, VAL_MAX, VAL_SPLIT } val_choice;

brancher new_int_brancher(var_choice, val_choice, intvar*, int);
brancher new_bool_brancher(var_choice, val_choice, atom*, int);
brancher seq_brancher(brancher*, int);
brancher limit_brancher(brancher);
void add_brancher(solver, brancher);

result solve(solver, int);

int post_atom(solver, atom);
int post_clause(solver, atom*, int);

int assume(solver, atom);
void retract(solver);

model get_model(solver);
void destroy_model(model);

int int_value(model, intvar);
int atom_value(model, atom);

int ivar_lb(intvar);
int ivar_ub(intvar);

atom ivar_le(intvar, int);
atom ivar_eq(intvar, int);

pred_t new_pred(solver, int, int);
atom pred_ge(pred_t, int);

statistics get_statistics(solver);

// Proof logging
void set_log_file(solver, FILE*);
void set_cons_id(solver, int);
#ifdef __cplusplus
}
#endif

#endif
