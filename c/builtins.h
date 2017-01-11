#ifndef PHAGE_C_BUILTINS_H
#define PHAGE_C_BUILTINS_H
#include "c/atom.h"
#include "c/phage.h"

#ifdef __cplusplus
extern "C" {
#endif

/* These return false on top-level failure. */
// int clause(solver s, atom* cl, int sz);

typedef struct {
  int c;
  intvar x; 
} int_linterm;

// These are half-reified.
// For strict versions, call with r = at_True
int linear_le(solver s, atom r, int_linterm* ts, int sz, int k);
int linear_ne(solver s, atom r, int_linterm* ts, int sz, int k);

typedef struct {
  int c;
  atom x;
} at_linterm;

int bool_linear_le(solver s, atom r, at_linterm* ts, int sz, int k);
int bool_linear_ne(solver s, atom r, at_linterm* ts, int sz, int k);

// r -> (x <= y + k)
int int_le(solver s, atom r, intvar x, intvar y, int k);
int int_ne(solver s, atom r, intvar x, intvar y);

int int_mul(solver s, atom r, intvar z, intvar x, intvar y);
int int_abs(solver s, atom r, intvar z, intvar x);

int int_max(solver s, atom r, intvar z, intvar* xs, int sz);

int int_element(solver s, atom r, intvar z, intvar i, int* elts, int sz);
int var_int_element(solver s, atom r, intvar z, intvar i, intvar* elts, int sz);
#ifdef __cplusplus
}
#endif

#endif
