//======== Implementation of compact-table constraints ============
// Registers a manager with the solver, so we can share most of the support structures.
#include "solver/solver_data.h"
#include "solver/solver_ext.h"
#include "engine/propagator.h"
#include "engine/propagator_ext.h"

#include "constraints/builtins.h"

#include "mtl/bool-set.h"
#include "utils/bitset.h"

using namespace geas;

using btset = bitset::bitset;
using namespace bitset;

struct table_info {
  struct val_info {
    unsigned int var;
    unsigned int val_id;
  };

  table_info(size_t _arity, size_t _num_tuples)
    : arity(_arity), num_tuples(_num_tuples)
    , domains(arity), supports(arity) {

  }

  size_t arity;
  size_t num_tuples;

  // Incoming/outgoing edges for each state
  // support_set* val_support;
  support_set& val_supports(size_t x, size_t k) { return supports[x][k]; }

  // Initial domains (and mappings from value-id to actual value)
  vec< vec<int> > domains;
  vec< vec<support_set> > supports;

  vec<int> vals_start;
  vec<val_info> val_index;
  // Scratch space
  // sparse_bitset mask;
};

table_info* construct_table_info(vec< vec<int> >& tuples) {
  assert(tuples.size() > 0);
  unsigned int sz(tuples.size());
  unsigned int arity(tuples[0].size());

  vec<int> tperm(tuples.size());
  for(int ii = 0; ii < tuples.size(); ii++)
    tperm[ii] = ii;
  
  table_info* ti(new table_info(arity, sz));

  // Compute the set of values & supports for each variable.
  for(unsigned int xi = 0; xi < arity; ++xi) {
    // Sort tuples by xi-value.
    ti->vals_start.push(ti->val_index.size());

    std::sort(tperm.begin(), tperm.end(),
      [&tuples, xi](int ii, int jj) {
        if(tuples[ii][xi] == tuples[jj][xi]) return ii < jj;
        return tuples[ii][xi] < tuples[jj][xi];
      });
    
    // Now we can iterate through, and collect (a) values, and (b) support tuples.
    int v(tuples[tperm[0]][xi]);
    vec<int> v_rows { tperm[0] };
    unsigned int k = 0;

    for(int ii = 1; ii < tperm.size(); ++ii) {
      int t(tperm[ii]);

      if(tuples[t][xi] != v) {
        // Finished supports for v.
        ti->val_index.push(table_info::val_info { xi, k });
        ti->domains[xi].push(v);
        ti->supports[xi].push(support_set(v_rows.begin(), v_rows.end()));

        ++k;
        v = tuples[t][xi];
        v_rows.clear();
      }
      v_rows.push(t);
    }
    ti->val_index.push(table_info::val_info { xi, k });
    ti->domains[xi].push(v);
    ti->supports[xi].push(support_set(v_rows.begin(), v_rows.end()));
  }
  return ti;
}

class table_manager : public solver_ext<table_manager> {
public:
  table_manager(solver_data* s) { }
  ~table_manager(void) {
    for(table_info* ti : tables)
      delete ti;     
  }
   
  // Don't bother doing CSE on tables, rely on the caller knowing
  // when tables are re-used.
  table_id build(vec< vec<int> >& tuples);
  table_info& lookup(table_id r) { return *(tables[r]); }
protected:
  vec<table_info*> tables;
};

table_id table_manager::build(vec< vec<int> >& tuples) {
  table_id id(tables.size());
  tables.push(construct_table_info(tuples));
  return id;
}

class compact_table : public propagator, public prop_inst<compact_table> {
  watch_result wakeup(int vi) {
    auto info(table.val_index[vi]);
    if(live_vals[info.var].elem(info.val_id)) {
      if(!changed_vars.elem(info.var)) {
        queue_prop();
        changed_vars.add(info.var);
        old_live[info.var] = live_vals[info.var].size();
        trail_push(s->persist, live_vals[info.var].sz);
      }
      live_vals[info.var].remove(info.val_id);

      dead_vals[dead_sz] = vi;
      set(dead_sz, dead_sz+1);
    }
    return Wt_Keep;
  }

  // Assumes ex_tuples has been initialized appropriately.
  void mk_expl(int dead_idx, vec<clause_elt>& expl) {
    // Walk through the available values
    for(unsigned int vi : dead_vals.slice(0, dead_idx)) {
      table_info::val_info info(table.val_index[vi]);
    
#if 1
      // If this value was supporting something, add it eagerly.
      support_set& ss(table.supports[info.var][info.val_id]);
      if(try_remove_bits(ex_tuples, ss)) {
        xs[info.var].explain_neq(table.domains[info.var][info.val_id], expl);
        if(ex_tuples.is_empty())
          return;
      }
#else
      xs[info.var].explain_neq(table.domains[info.var][info.val_id], expl);
      ex_tuples.clear();
#endif
    }
    assert(ex_tuples.is_empty());
  }

  void ex_val(int dead_idx, pval_t _pi, vec<clause_elt>& expl) {
    unsigned int vi(dead_vals[dead_idx]);
    
    // Collect the set of tuples we need to explain.
    table_info::val_info ex_info(table.val_index[vi]);
    ex_tuples.init(table.supports[ex_info.var][ex_info.val_id]);
    mk_expl(dead_idx, expl);
  }

  void ex_fail(vec<clause_elt>& expl) {
    ex_tuples.fill(table.num_tuples);
    mk_expl(dead_sz, expl);
  }

public:
  compact_table(solver_data* s, table_id t, vec<intvar>& _xs)
    : propagator(s), table(table_manager::get(s)->lookup(t)), xs(_xs)
    , live_vals(xs.size())
    , live_tuples(table.num_tuples)
    , live_r(0)
    , residual(table.val_index.size(), 0)
    , active_vars(xs.size())
    , dead_vals(table.val_index.size(), 0)
    , dead_sz(0)
    , changed_vars(xs.size())
    , old_live(xs.size(), 0)
    , ex_tuples(table.num_tuples) {

    live_tuples.fill(table.num_tuples);

    for(int xi : irange(xs.size())) {
      vec<int>& d(table.domains[xi]);
      make_sparse(xs[xi], d);
      live_vals[xi].growTo(d.size());
      for(int k : irange(d.size())) {
        if(in_domain(xs[xi], d[k])) {
          attach(s, xs[xi] != d[k], watch<&P::wakeup>(table.vals_start[xi] + k));
          live_vals[xi].insert(k);
        } else {
          dead_vals[dead_sz] = table.vals_start[xi] + k;  
          dead_sz.x = dead_sz + 1;
        }
      }
      if(live_vals.size() > 1)
        active_vars.insert(xi);

      if(live_vals[xi].size() != (unsigned int) d.size()) {
        changed_vars.add(xi);
        old_live[xi] = d.size();
      }
    }
    queue_prop();
  }


  bool filter(vec<clause_elt>& confl) {
    // Iterate in reverse, so we can safely remove values.
    unsigned int act_sz = active_vars.size();
    for(unsigned int x : active_vars.rev()) {
      unsigned int x_sz = live_vals[x].size();
      for(unsigned int k : live_vals[x].rev()) {
        // Check if there is still some support for x = k.
        support_set& ss(table.supports[x][k]);
        auto r(ss[residual[table.vals_start[x] + k]]);        

        if(live_tuples[r.w] & r.bits)
          goto next_value;

        // Otherwise, search for a new support.
        {
        auto b(ss.begin());
        auto e(ss.end());

          for(; b != e; ++b) {
            if(live_tuples[(*b).w] & (*b).bits) {
              // Found a new support
              residual[table.vals_start[x] + k] = (b - ss.begin());   
              goto next_value;
            }
          }
        }
        // No supports left. Try removing it from the domain of x.
        dead_vals[dead_sz] = table.vals_start[x] + k;
        if(!enqueue(*s, xs[x] != table.domains[x][k], expl<&P::ex_val>(dead_sz))) {
          active_vars.sz = act_sz;
          live_vals[x].sz = x_sz;
          return false;
        }
        set(dead_sz, dead_sz+1);
        live_vals[x].remove(k);
    next_value:
        continue;
      }
      // If some value was killed, make sure it'll get restored on backtracking.
      if(live_vals[x].size() != x_sz) {
        trail_fake(s->persist, live_vals[x].sz, x_sz);
        // If x is now fixed, we never need to check it again.
        if(live_vals[x].size() == 1) {
          trail_push(s->persist, active_vars.sz);
          active_vars.remove(x);
        }
      }
    }
    // If some variable was disabled, save the old value
    if(active_vars.size() != act_sz)
      trail_fake(s->persist, active_vars.sz, act_sz);
    return true;
  }

  void update_tuples(void) {
    for(unsigned int x : changed_vars) {
      p_sparseset& x_vals(live_vals[x]);
      // Ignore resetting for now.

      for(unsigned int k : x_vals.slice(x_vals.size(), old_live[x])) {
        kill_value(x, k);
      }
    }
    changed_vars.clear();
  }

  bool tuples_nonempty(void) {
    if(live_tuples[live_r])
      return true;
    for(int w : irange(live_tuples.size())) {
      if(live_tuples[w]) {
        live_r = w;
        return true;
      }
    }
    return false;
  }

  bool propagate(vec<clause_elt>& confl) {
    update_tuples();
    if(!tuples_nonempty()) {
      ex_fail(confl);
      return false;
    }
    if(!filter(confl))
      return false;

    return true;
  }
   
  void cleanup(void) {
    is_queued = false;
    changed_vars.clear();
  }

protected:
  // Compute S - T, returning true if S changed (so S & T was non-empty).
  bool try_remove_bits(p_sparse_bitset& bits, support_set& rem) {
    auto it(rem.begin());
    auto en(rem.end());
    // Search for a word with non-empty intersection with bits.
    for(; it != en; ++it) {
      unsigned int w((*it).w);
      if(!bits.idx.elem(w))
        continue;
      if(bits[w] & (*it).bits) {
        // Non-empty. Remove bits in this word...
        word_ty r(bits[w] & ~(*it).bits);
        bits[w] = r;
        if(!r) bits.idx.remove(w);

        // And any remaining words.
        for(++it; it != en; ++it) {
          unsigned int w((*it).w);
          if(!bits.idx.elem(w))
            continue;
          word_ty r(bits[w] & ~(*it).bits);
          bits[w] = r;
          if(!r) bits.idx.remove(w);
        }
        return true;
      }
    }
    return false;
  }

  inline void word_remove(btset& bits, support_set::elem_ty e) {
    if(bits[e.w] & e.bits) {
      trail_change(s->persist, bits[e.w], bits[e.w] & ~e.bits);
    }
  }

  void kill_value(unsigned int x, unsigned int k) {
    support_set& ss(table.supports[x][k]);
    for(support_set::elem_ty e : ss) {
      word_remove(live_tuples, e);
    }
  }

  // The pre-computed table information
  table_info& table;

  // Parameters
  vec<intvar> xs;

  // Persistent state
  vec<p_sparseset> live_vals;
  btset live_tuples;
  unsigned int live_r;

  vec<unsigned int> residual;
  p_sparseset active_vars;

  // We use dead_vals to reconstruct
  // the state upon explanation.
  vec<unsigned int> dead_vals;
  Tint dead_sz;

  // Transient data
  boolset changed_vars;
  vec<unsigned int> old_live;

  p_sparse_bitset ex_tuples;
};

namespace geas {

namespace table {
  table_id build(solver_data* s, vec< vec<int> >& rows) {
    return table_manager::get(s)->build(rows);    
  }
  bool post(solver_data* s, table_id t, vec<intvar>& xs) {
    return compact_table::post(s, t, xs);
  }
}

}
