#include "mtl/Vec.h"
#include "utils/defs.h"

#include "c/atom.h"
#include "c/phage.h"
#include "c/builtins.h"

#include "c/marshal.h"

#include "solver/solver_data.h"
#include "constraints/builtins.h"
#include "constraints/flow/flow.h"

#ifdef __cplusplus
extern "C" {
#endif

/*
int clause(solver s, atom* cl, int sz) {
  vec<phage::clause_elt> elts;
  for(int ii : irange(sz))
    elts.push(get_atom(cl[ii]));
  return add_clause(*get_solver(s)->data, elts);
}
*/

// These are half-reified.
// For strict versions, call with r = at_True
int linear_le(solver s, atom r, int_linterm* ts, int sz, int k) {
  vec<int> ks;
  vec<phage::intvar> xs;
  for(int ii = 0; ii < sz; ii++) {
    ks.push(ts[ii].c);
    xs.push(*get_intvar(ts[ii].x));
  }
#if 0
  if(xs.size() > 5)
    return phage::linear_le_ps(get_solver(s)->data, ks, xs,  k, get_atom(r));
  else
    return phage::linear_le(get_solver(s)->data, ks, xs,  k, get_atom(r));
#else
  return phage::linear_le(get_solver(s)->data, ks, xs,  k, get_atom(r));
#endif

}

int linear_ne(solver s, atom r, int_linterm* ts, int sz, int k) {
  vec<int> ks;
  vec<phage::intvar> xs;
  for(int ii = 0; ii < sz; ii++) {
    ks.push(ts[ii].c);
    xs.push(*get_intvar(ts[ii].x));
  }
  return phage::linear_ne(get_solver(s)->data, ks, xs,  k, get_atom(r));
}

int bool_linear_le(solver s, atom r, at_linterm* ts, int sz, int k) {
  vec<int> ks;
  vec<phage::patom_t> xs;
  for(int ii = 0; ii < sz; ii++) {
    ks.push(ts[ii].c);
    xs.push(get_atom(ts[ii].x));
  }
  return phage::bool_linear_le(get_solver(s)->data, ks, xs,  k, get_atom(r));
}
int atmost_1(solver s, atom r, atom* xs, int sz) {
  vec<phage::patom_t> ys;
  for(int ii : irange(sz))
    ys.push(get_atom(xs[ii]));
  return phage::atmost_1(get_solver(s)->data, ys, get_atom(r));
}

int atmost_k(solver s, atom r, atom* xs, int sz, int k) {
  vec<phage::patom_t> ys;
  for(int ii : irange(sz))
    ys.push(get_atom(xs[ii]));
  return phage::atmost_k(get_solver(s)->data, ys, k, get_atom(r));
}

int bool_linear_ne(solver s, atom r, at_linterm* ts, int sz, int k) {
  vec<int> ks;
  vec<phage::patom_t> xs;
  for(int ii = 0; ii < sz; ii++) {
    ks.push(ts[ii].c);
    xs.push(get_atom(ts[ii].x));
  }
  return phage::bool_linear_ne(get_solver(s)->data, ks, xs,  k, get_atom(r));
}


int int_mul(solver s, atom r, intvar z, intvar x, intvar y) {
  return phage::int_mul(get_solver(s)->data,
                        *get_intvar(z), *get_intvar(x), *get_intvar(y),
                        get_atom(r));
}
int int_div(solver s, atom r, intvar z, intvar x, intvar y) {
  return phage::int_div(get_solver(s)->data,
                        *get_intvar(z), *get_intvar(x), *get_intvar(y),
                        get_atom(r));
}

int int_abs(solver s, atom r, intvar z, intvar x) {
  return phage::int_abs(get_solver(s)->data,
                        *get_intvar(z), *get_intvar(x), get_atom(r));
}

int int_max(solver s, atom r, intvar z, intvar* xs, int sz) {
  vec<phage::intvar> p_xs;
  for(intvar* v = xs; v != xs+sz; ++v) {
    p_xs.push(*get_intvar(*v));
  }
  return phage::int_max(get_solver(s)->data,
                        *get_intvar(z), p_xs, get_atom(r));
}

int int_element(solver s, atom r, intvar z, intvar x, int* elts, int sz) {
  vec<int> p_elts;
  for(int* v = elts; v != elts+sz; ++v) {
    p_elts.push(*v);
  }
  return phage::int_element(get_solver(s)->data,
                        *get_intvar(z), *get_intvar(x), p_elts, get_atom(r));
}

int var_int_element(solver s, atom r, intvar z, intvar x, intvar* elts, int sz) {
  vec<phage::intvar> p_elts;
  for(intvar* v = elts; v != elts+sz; ++v) {
    p_elts.push(*get_intvar(*v));
  }
  return phage::var_int_element(get_solver(s)->data,
                        *get_intvar(z), *get_intvar(x), p_elts, get_atom(r));
}

int int_le(solver s, atom r, intvar x, intvar y, int k) {
  return phage::int_le(get_solver(s)->data,
                    *get_intvar(x), *get_intvar(y), k, get_atom(r));
}

int int_ne(solver s, atom r, intvar x, intvar y) {
  return phage::int_ne(get_solver(s)->data,
                    *get_intvar(x), *get_intvar(y), get_atom(r));
}
int int_eq(solver s, atom r, intvar x, intvar y) {
  return phage::int_eq(get_solver(s)->data,
                    *get_intvar(x), *get_intvar(y), get_atom(r));
}

int all_different_int(solver s, intvar* xs, int sz) {
  vec<phage::intvar> p_xs;
  for(intvar* v = xs; v != xs+sz; ++v) {
    p_xs.push(*get_intvar(*v));
  }
#if 0
  return phage::all_different_int(get_solver(s)->data, p_xs);
#else
  /*
  vec<int> ds(p_xs.size(), 1);
  return phage::disjunctive_int(get_solver(s)->data, p_xs, ds);
  */
  // Find the min and max-domains.
  phage::solver_data* sd(get_solver(s)->data);
  int lb = p_xs[0].lb(sd); 
  int ub = p_xs[0].ub(sd); 
  for(int ii = 1; ii < p_xs.size(); ii++) {
    lb = std::min(lb, (int) p_xs[ii].lb(sd));
    ub = std::max(ub, (int) p_xs[ii].ub(sd));
  }

  int dom = ub - lb + 1;
  if(p_xs.size() == dom) {
    vec<int> srcs(p_xs.size(), 1);
    vec<int> sinks(p_xs.size(), 1);

    vec<phage::bflow> flows;
    for(int xi : irange(p_xs.size())) {
      for(int k : irange(dom)) {
        flows.push(phage::bflow {xi, k, p_xs[xi] == lb+k }); 
      }
    }
    return phage::bipartite_flow(sd, srcs, sinks, flows);
  } else {
    return phage::all_different_int(sd, p_xs);
  }
#endif
}

int bipartite_flow(solver s, int* srcs, int srcs_sz, int* sinks, int sinks_sz, bp_flow* flows, int flows_sz) {
  vec<int> src_vec;
  for(; srcs_sz; --srcs_sz, ++srcs)
    src_vec.push(*srcs);

  vec<int> sink_vec; 
  for(; sinks_sz; --sinks_sz, ++sinks)
    sink_vec.push(*sinks);

  vec<phage::bflow> flow_vec;
  for(; flows_sz; --flows_sz, ++flows) {
    flow_vec.push(phage::bflow { (*flows).src, (*flows).sink, get_atom((*flows).at) });
  }
  return phage::bipartite_flow(get_solver(s)->data, src_vec, sink_vec, flow_vec);
}

int cumulative(solver s, task* ts, int sz, int cap) {
  vec<phage::intvar> xs;
  vec<int> ds;
  vec<int> rs;
  for(task t : range(ts, ts+sz)) {
    xs.push(*get_intvar(t.start));
    ds.push(t.dur);
    rs.push(t.res);
  }
  return phage::cumulative(get_solver(s)->data, xs, ds, rs, cap);
}
int disjunctive(solver s, dtask* ts, int sz) {
  vec<phage::intvar> xs;
  vec<int> ds;
  for(dtask t : range(ts, ts+sz)) {
    xs.push(*get_intvar(t.start));
    ds.push(t.dur);
  }
  return phage::disjunctive_int(get_solver(s)->data, xs, ds);
}

#ifdef __cplusplus
}
#endif
