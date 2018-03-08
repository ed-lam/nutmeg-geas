#include <cassert>
#include <map>
#include "mtl/Vec.h"
#include "solver/solver_data.h"
#include "constraints/builtins.h"

namespace geas {

struct term {
  int c;
  patom_t x;
};

struct {
  int operator()(const term& a, const term& b) const {
    return a.c > b.c;
  }
} term_lt;

bool atmost_1(solver_data* s, vec<patom_t>& xs, patom_t r) {
  // ps[ii] is the index of the true element.
  pid_t ps = new_pred(*s, 0, xs.size()-1); 
  for(int ii : irange(xs.size())) {
    if(!add_clause(s, ~r, ge_atom(ps, ii), ~xs[ii]))
      return false;
    if(!add_clause(s, ~r, le_atom(ps, ii), ~xs[ii]))
      return false;
  }
  return true;
}

bool atmost_k(solver_data* s, vec<patom_t>& xs, int k, patom_t r) {
  pid_t ps = new_pred(*s, 0, xs.size()-1);
  for(int xi : irange(xs.size())) {
    if(!add_clause(s, ~r, le_atom(ps, xi), ~xs[xi]))
      return false;
  }
  for(int ki = 1; ki < k; ki++) {
    pid_t qs = new_pred(*s, 0, xs.size()-1);
    for(int xi : irange(xs.size())) {
      if(!add_clause(s, ~r, ge_atom(ps, xi), le_atom(qs, xi), ~xs[xi]))
        return false;
    }
    ps = qs;
  }
  for(int xi : irange(xs.size())) {
    if(!add_clause(s, ~r, ge_atom(ps, xi), ~xs[xi]))
      return false;
  }
  return true;
}

int normalize_terms(vec<int>& cs, vec<patom_t>& xs, vec<term>& ts) {
  int shift = 0; 
  for(int ii : irange(cs.size())) {
    if(cs[ii] > 0) {
      ts.push(term { cs[ii], xs[ii] });
    } else if(cs[ii] < 0) {
      // -k b == -k + k (~b)
      ts.push(term { -cs[ii], ~xs[ii] });
      shift -= cs[ii];
    }
  }
  return shift;
}

bool bool_linear_le(solver_data* s, vec<int>& cs, vec<patom_t>& xs, int k, patom_t r) {
  // Normalize coefficients to positive
  vec<term> ts;
  int shift = normalize_terms(cs, xs, ts);
  k += shift;
  
  // Sort by coefficients
  std::sort(ts.begin(), ts.end(), term_lt);
  assert(k >= 0);
    
  // No half reification?
  assert(s->state.is_entailed(r));

  // Waste to use intvars -- just preds
  // Offset everything by k to avoid underflow
  int off = k;
  vec<pid_t> sums;
  for(int ii = 1; ii < xs.size(); ii++) {
    sums.push(new_pred(*s, off, off + k));
  }

  if(!add_clause(s, ~ts[0].x, ge_atom(sums[0], off + ts[0].c))) // Should only fail if ts[0].x && c > k.
    return false;
  for(int ii = 1; ii < xs.size()-1; ii++) {
    if(!pred_le(s, sums[ii-1], sums[ii], 0))
      return false;
    if(!pred_le(s, sums[ii-1], sums[ii], -ts[ii].c, ts[ii].x))
      return false;
  }
  if(!add_clause(s, ~ts.last().x, le_atom(sums.last(), off + k - ts.last().c)))
    return false;

  return true; 
}

bool bool_linear_ne(solver_data* s, vec<int>& ks, vec<patom_t>& xs, int k, patom_t r) {
  assert(0);
  return true;
}

};
