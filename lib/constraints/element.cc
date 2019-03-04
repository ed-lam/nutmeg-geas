#include <utility>
#include <algorithm>
#include <climits>
#include <geas/engine/propagator.h>
#include <geas/engine/propagator_ext.h>
#include <geas/solver/solver_data.h>
#include <geas/vars/intvar.h>

#include <geas/utils/interval.h>
#include <geas/mtl/p-sparse-set.h>
#include <geas/mtl/support-list.h>

// #define DEBUG_ELEM

namespace geas {

typedef std::pair<int, int> ipair;

struct sort_occ {
  bool operator()(int xi, int xj) const {
    if(ys[xi] == ys[xj])
      return xi < xj;
    return ys[xi] < ys[xj];
  }
  vec<int>& ys;
};

// Propagator, for when the array of interest is large: we propagate only
// bounds of x.
#define ELEM_DOM_SWAP
class int_elem_dom : public propagator, public prop_inst<int_elem_dom> {
  struct row {
    int val; 
    patom_t at;
    vec<int> occurs; // occurs[0] is the current watch.
#ifndef ELEM_DOM_SWAP
    Tint occ_start;
#endif
  };

  watch_result wake_x(int xi) {
    // Check if ys[xi] has another support
    int ri = vals[xi];
    row& r(rows[ri]);
    assert(r.occurs[0] == xi);
    // for(int jj : irange(1, r.occurs.size())) {
#ifdef ELEM_DOM_SWAP
    int start = 1;
#else
    int start = r.occ_start;
#endif
    for(int jj : irange(start, r.occurs.size())) {
      int xj = r.occurs[jj];
      if(!s->state.is_inconsistent(atoms[xj])) {
        // Appropriate replacement found. Replace this
        // watch.
#ifdef ELEM_DOM_SWAP
        r.occurs[jj] = r.occurs[0];
        r.occurs[0] = xj;
#else
        r.occ_start.set(s->persist, jj);
#endif
        attach(s, ~atoms[xj], watch<&P::wake_x>(xj, Wt_IDEM));
        return Wt_Drop;
      }
    }
    expired_rows.push(ri);
    queue_prop();
    return Wt_Keep;
  }

  watch_result wake_z(int ri) {
    expired_rows.push(ri); 
    queue_prop();
    return Wt_Keep;
  }
  
  void ex_z(int ri, pval_t _p, vec<clause_elt>& expl) {
    for(int xi : rows[ri].occurs)
      expl.push(atoms[xi]); 
  }

  void init_rows(intvar z, vec<int>& occ, vec<int>& ys, vec<row>& rows) {
    int z_curr = ys[occ[0]];
#ifdef ELEM_DOM_SWAP
    rows.push({ z_curr, z == z_curr, vec<int>() });
#else
    rows.push({ z_curr, z == z_curr, vec<int>(), 0 });
#endif

    for(int xi : occ) {
      int zval = ys[xi];
      
      if(zval != z_curr) {
#ifdef ELEM_DOM_SWAP
        rows.push({ zval, z == zval, vec<int>() });
#else
        rows.push({ zval, z == zval, vec<int>(), 0 });
#endif
//        rows.push();
//        rows.last().val = zval;
//        rows.last().at = (z == zval);
        z_curr = zval;
      }
      rows.last().occurs.push(xi);
    }
  }
public:  
  int_elem_dom(solver_data* s, intvar _z, vec<int>& _ys, intvar _x)
    : propagator(s), z(_z), x(_x), vals(_ys.size(), 0) {
    // Invert ys to get occurrence lists.
    vec<int> ys(_ys);
    for(int xi : irange(ys.size()))
      atoms.push(x == xi);
    vec<int> occ(irange(ys.size()).to_vec());
    std::sort(occ.begin(), occ.end(), sort_occ { ys });

    // Set up the rows
    init_rows(z, occ, ys, rows); 
    // ...then filter the domain of z... 
    uniq(ys); make_sparse(z, ys);
    // ...and set up the cross-references and watches
    for(int ri : irange(rows.size())) {
      int wx = rows[ri].occurs[0];
      attach(s, ~rows[ri].at, watch<&P::wake_z>(ri, Wt_IDEM));
      attach(s, ~atoms[wx], watch<&P::wake_x>(wx, Wt_IDEM));
      for(int xi : rows[ri].occurs)
        vals[xi] = ri;
    }
  }
  bool propagate(vec<clause_elt>& confl) {
    for(int ri : dying_rows) {
      if(!enqueue(*s, ~rows[ri].at, ex_thunk(ex<&P::ex_z>, ri)))
        return false;
    }

    for(int ri : expired_rows) {
      patom_t r(rows[ri].at);
      for(int xi : rows[ri].occurs) {
        if(!enqueue(*s, ~atoms[xi], r))
          return false;
      }
    }
    dying_rows.clear();
    expired_rows.clear();
    return true;
  }

  void cleanup(void) {
    is_queued = false;
    dying_rows.clear();
    expired_rows.clear();
  }

  intvar z;
  intvar x;

  vec<row> rows; // For each z-val, the corresponding xs.
  vec<int> vals; // For each x, the corresponding row.
  vec<patom_t> atoms; // For each x, the x=k atom.
  
  // Transient state
  vec<int> dying_rows;
  vec<int> expired_rows;
};

class int_elem_bnd : public propagator, public prop_inst<int_elem_bnd> {
  static int prop_count;
  enum { C_NONE = 0, C_LB = 1, C_UB = 2, C_LB_ROW = 4, C_UB_ROW = 8 };

  struct row {
    int val; // z-val
    Tint begin;
    Tint end;
    int supp_idx;
    vec<int> occurs; // occurrences
  };

  inline void kill_row(int row) {
    trail_save(s->persist, live_rows.sz, live_saved);
    live_rows.remove(row);
  }

  watch_result wake_x_lb(int _x) {
    if(!(change&C_LB)) {
      change |= C_LB;
      lb_prev = x.lb(s->wake_vals);
      queue_prop();
    }
    return Wt_Keep;
  }
  watch_result wake_x_ub(int _x) {
    if(!(change&C_UB)) {
      change |= C_UB;
      ub_prev = x.ub(s->wake_vals);
      queue_prop();
    }
    return Wt_Keep;
  }

  watch_result wake_z(int r) {
    // FIXME: Find out why wake_z is called
    // with already-dead rows
    if(live_rows.elem(r)) {
      kill_row(r);
      int l = lb(x);
      if(r == vals[l]) {
        change |= C_LB_ROW;      
        queue_prop();
      }
      int u = ub(x);
      if(r == vals[u]) {
        change |= C_UB_ROW;
        queue_prop();
      }
    }
    return Wt_Keep;
  }

  void ex_z(int ri, pval_t _p, vec<clause_elt>& expl) {
    // z is explained by the gap between consecutive occurrences.
    row& r(rows[ri]);
    if(r.end > 0)
      expl.push(x <= r.occurs[r.end-1]);
    if(r.end < r.occurs.size())
      expl.push(x >= r.occurs[r.end]);
  }

  void ex_x_lb(int live_sz, pval_t p, vec<clause_elt>& expl) {
    int x_lb = x.lb_of_pval(p);

    int x_suff = lb_0(x)-1;
    // For each live row...
    for(int ridx : irange(live_sz)) {
      int ri = live_rows[ridx];
      row& r(rows[ri]);
      // ...find the largest supported value below x_lb.
      int start = 0;
      int end = r.end;
      while(start < end) {
        int mid = start + (end - start)/2;
        if(r.occurs[mid] >= x_lb)
          end = mid;
        else
          start = mid+1;
      }
      if(start > 0 && r.occurs[start-1] > x_suff)
        x_suff = r.occurs[start-1];   
    }

    for(int ridx : irange(live_sz, rows.size())) {
      int ri = live_rows[ridx];
      // Now check which rows need to be included in the explanation.
      // Any rows without occurrences in [x_suff+1, x_lb] can be discarded.
      row& r(rows[ri]);
      int start = 0;
      int end = r.occurs.size();
      while(start < end) {
        int mid = start + (end - start)/2;

        if(r.occurs[mid] > x_lb)
          end = mid;
        else if(r.occurs[mid] < x_suff)
          start = mid+1;
        else {
          // We've found some value inside the forbidden region.
          expl.push(z == r.val);
          break;
        }
      }
    }
    expl.push(x <= x_suff);
  }
   
  void ex_x_ub(int live_sz, pval_t p, vec<clause_elt>& expl) {
    int x_ub = x.ub_of_pval(p);

    int x_suff = ub_0(x)+1;
    // For each live row...
    for(int ridx : irange(live_sz)) {
      int ri = live_rows[ridx];
      row& r(rows[ri]);
      // ...find the largest supported value below x_lb.
      int start = r.begin;
      int end = r.occurs.size();
      while(start < end) {
        int mid = start + (end - start)/2;
        if(r.occurs[mid] <= x_ub)
          start = mid+1;
        else
          end = mid;
      }
      if(start < r.occurs.size() && r.occurs[start] < x_suff)
        x_suff = r.occurs[start];
    }
    assert(x_suff > x_ub);

    for(int ridx : irange(live_sz, rows.size())) {
      int ri = live_rows[ridx];
      // Now check which rows need to be included in the explanation.
      // Any rows without occurrences in [x_suff+1, x_lb] can be discarded.
      row& r(rows[ri]);
      int start = 0;
      int end = r.occurs.size();
      while(start < end) {
        int mid = start + (end - start)/2;

        if(r.occurs[mid] > x_suff)
          end = mid;
        else if(r.occurs[mid] <= x_ub)
          start = mid+1;
        else {
          // We've found some value inside the forbidden region.
          expl.push(z == r.val);
          break;
        }
      }
    }
    expl.push(x >= x_suff);
  }
  
  void init_rows(vec<int>& ys, vec<row>& rows) {
    // Sort occurrences by the corresponding y-value.
    vec<int> occ(irange(ys.size()).to_vec());
    std::sort(occ.begin(), occ.end(), sort_occ {ys});

    int curr_z = ys[occ[0]];
    rows.push(row { curr_z, 0, 0, 0, vec<int>() });
    rows.last().occurs.push(occ[0]);
    for(int ii : irange(1, occ.size())) {
      int yi = occ[ii];
      if(ys[yi] != curr_z) {
        rows.last().end.x = rows.last().occurs.size();

        curr_z = ys[yi];
        rows.push(row { curr_z, 0, 0, 0, vec<int>() });
      }
      rows.last().occurs.push(yi);
    }
    rows.last().end.x = rows.last().occurs.size();
  }

public:
  int_elem_bnd(solver_data *s, patom_t _r, intvar _z, intvar _x, vec<int>& _ys)
    : propagator(s), z(_z), x(_x), vals(_ys.size(), 0),
      live_saved(0),
      change(0) {
    assert(s->state.is_entailed(_r)); // FIXME: Implement half-reified element
    
    // Compute the set of live values, and their occurrences. 
    vec<int> ys(_ys);
    init_rows(ys, rows);
    live_rows.growTo(rows.size()); live_rows.sz = rows.size();

    uniq(ys);
    make_sparse(z, ys);

    // Now set the cross-references
    for(int ri : irange(rows.size())) {
      row& r(rows[ri]);
      for(int xi : r.occurs)
        vals[xi] = ri;
    }

    // And attach the propagator
    x.attach(E_LB, watch<&P::wake_x_lb>(0, Wt_IDEM));
    x.attach(E_UB, watch<&P::wake_x_ub>(0, Wt_IDEM));
    for(int ri : irange(rows.size())) {
      row& r(rows[ri]);
      attach(s, z != r.val, watch<&P::wake_z>(ri, Wt_IDEM));
    }
  }
  
  // Check if the current row is still supported.
  bool update_row(int ri, vec<clause_elt>& confl) {
    row& r(rows[ri]);
    int l = lb(x); int u = ub(x);
    int begin = r.begin;
    int end = r.end;

    int supp = r.occurs[r.supp_idx];
    if(supp < l) {
      begin = r.supp_idx+1;
    } else if(supp > u) {
      end = r.supp_idx;
    } else {
      return true;
    }
    
    while(begin != end) {
      int mid = begin + (end - begin)/2;
      int xval = r.occurs[mid];
      if(xval < l) {
        begin = mid+1;
      } else if(u < xval) {
        end = mid;
      } else {
        r.supp_idx = mid;
        break;
      }
    }
    if(begin != r.begin)
      r.begin.set(s->persist, begin);
    if(end != r.end)
      r.end.set(s->persist, end);

    if(begin == end) {
      if(!enqueue(*s, z != r.val, ex_thunk(ex<&P::ex_z>, ri)))
        return false;
      //live_rows.remove(ri);
      kill_row(ri);
    }
    return true;
  }

  bool propagate(vec<clause_elt>& confl) {
      prop_count++;
    if(change&(C_LB|C_UB)) {
      int l = lb(x); int u = ub(x);
      unsigned int scan_sz = 0;
      if(change&C_LB)
        scan_sz += l - lb_prev;
      if(change&C_UB)
        scan_sz += ub_prev - u;
      if(scan_sz < live_rows.size()) {
        // If the bounds only moved a little,
        // check which 
        if(change&C_LB) {
          for(int k : irange(lb_prev, l)) {
            if(!live_rows.elem(vals[k]))
              continue;
            if(!update_row(vals[k], confl))
              return false;
          }
        }
        if(change&C_UB) {
          for(int k : irange(u+1, ub_prev+1)) {
            if(!live_rows.elem(vals[k]))
              continue;
            if(!update_row(vals[k], confl))
              return false;
          }
        }
      } else {
        // If we've jumped too many values, just
        // iterate over the live rows.
        // for(int ii : irange(live_rows.size())) {
        // Run backwards, because of how p_sparseset removal works.
        for(int ii = live_rows.size()-1; ii >= 0; --ii) {
          if(!update_row(live_rows[ii], confl))
            return false;
        }
      }
    }

    if(change&(C_LB|C_LB_ROW)) {
      int l = x.lb(s); int u = x.ub(s);
      // Walk the lb up to the next supported value
      for(; l <= u; ++l) {
        if(live_rows.elem(vals[l]))
          break;
      }
      if(!set_lb(x, l, ex_thunk(ex<&P::ex_x_lb>, live_rows.sz)))
        return false;
    }
    
    if(change&(C_UB|C_UB_ROW)) {
      int l = x.lb(s); int u = x.ub(s);
      // Walk the ub down to the nearest
      // supported value
      for(; l <= u; --u) {
        if(live_rows.elem(vals[u]))
          break;
      }
      if(!set_ub(x, u, ex_thunk(ex<&P::ex_x_ub>, live_rows.sz)))
        return false;
    }
    return true;
  }

  void cleanup(void) {
    is_queued = false;
    change = C_NONE;
  }

  // Problem specification
  intvar z;
  intvar x;
  vec<row> rows;
  vec<int> vals;

  // Persistent state
  p_sparseset live_rows;
  char live_saved;

  // Transient state
  unsigned char change; 
  // Track which values we
  // need to check.
  int lb_prev;
  int ub_prev;
};

bool int_element(solver_data* s, patom_t r, intvar z, intvar x,
                   vec<int>& ys, int base) {
  // Also set domain of ys.
  vec<int> ys_uniq(ys);
  uniq(ys_uniq);

  if(s->state.is_entailed_l0(r)) {
    if(base > x.lb(s))
      enqueue(*s, x >= base, reason());
    if(base + ys.size() <= x.ub(s))
      enqueue(*s, x <= base + ys.size()-1, reason());
    // z.set_lb(ys_uniq[0], reason()); z.set_ub(ys_uniq.last(), reason());

    if(!make_sparse(z, ys_uniq))
      return false;
  } else {
    if(!add_clause(s, ~r, x >= base))
      return false;
    if(!add_clause(s, ~r, x < base + ys.size()))
      return false;

    vec<clause_elt> ps { ~r };
    for(int y : ys)
      ps.push(z == y);
    if(!add_clause(*s, ps))
      return false;
  }

  for(int ii : irange(ys.size())) {
    if(!add_clause(s, ~r, x != ii + base, z == ys[ii]))
      return false;
  }

  // vec<int> ys_uniq(ys); uniq(ys_uniq);

  for(int yy : ys_uniq) {
    vec<clause_elt> ps { ~r, z != yy };
//    ps.push(z != yy);
    for(int ii : irange(ys.size())) {
      if(ys[ii] == yy) {
        ps.push(x == ii + base);
      }
    }
    if(!add_clause(*s, ps))
      return false;
  }

  return true;
}

class elem_var_bnd : public propagator, public prop_inst<elem_var_bnd> {
  // Wakeup and explanation
  static void ex_naive(elem_var_bnd* p, int yi, vec<clause_elt>& expl) {
    expl.push(p->x < p->x.lb(p->s));
    expl.push(p->x > p->x.ub(p->s));
    expl.push(p->z < p->z.lb(p->s));
    expl.push(p->z > p->z.ub(p->s));
    for(intvar& y : p->ys) {
      expl.push(y < y.lb(p->s));
      expl.push(y > y.ub(p->s));
    }
  }

  void ex_y_lb(int yi, pval_t p, vec<clause_elt>& expl) {
    int lb = ys[yi].lb_of_pval(p);
    // expl.push(x < yi + base);
    // expl.push(x > yi + base);
    x.explain_eq(yi+base, expl);
    expl.push(z < lb);
  }

  void ex_y_ub(int yi, pval_t p, vec<clause_elt>& expl) {
    int ub = ys[yi].ub_of_pval(p);
    // expl.push(x < yi + base);
    // expl.push(x > yi + base);
    x.explain_eq(yi+base, expl);
    expl.push(z > ub);
  }
   
  void ex_x_lb(int vi, pval_t p, vec<clause_elt>& expl) {
    expl.push(x < vi+base);
    push_hints(vi, x.lb_of_pval(p) - base, expl);
  }

  void ex_x_ub(int vi, pval_t p, vec<clause_elt>& expl) {
    expl.push(x > vi+base);
    push_hints(x.ub_of_pval(p)-base+1, vi+1, expl);
  }

  /*
  static void ex_z(void* ptr, int pos, pval_t pval, vec<clause_elt>& expl) {
    GEAS_NOT_YET;
  }
  */
  void ex_z_lb(int _vi, pval_t p, vec<clause_elt>& expl) {
    // fprintf(stderr, "elem_bnd::ex::lb(z)\n");
    intvar::val_t z_lb = z.lb_of_pval(p);

    EX_PUSH(expl, x < lb(x));
    EX_PUSH(expl, x > ub(x));

    intvar::val_t z_step = lb_0(z)-1;
    vec<int> step_idxs;
    for(int yi = lb(x) - base; yi <= ub(x) - base; yi++) {
      if(ub(ys[yi]) < z_lb) {
        z_step = std::max(z_step, ub(ys[yi]));
        step_idxs.push(yi);
      } else
        EX_PUSH(expl, ys[yi] < z_lb);
    }
    /*
    if(z_step > lb_0(z))
      expl.push(z <= z_step);
      */
    if(step_idxs.size() > 0) {
      EX_PUSH(expl, z <= z_step);
      for(int yi : step_idxs) {
        EX_PUSH(expl, ys[yi] > z_step);
      }
    }
  }

  void ex_z_ub(int _vi, pval_t p, vec<clause_elt>& expl) {
    // fprintf(stderr, "elem_bnd::ex::ub(z)\n");
    int z_ub = z.ub_of_pval(p); 

    EX_PUSH(expl, x < lb(x));
    EX_PUSH(expl, x > ub(x));

    intvar::val_t z_step = ub_0(z)+1;
    vec<int> step_idxs;
    for(int yi = lb(x) - base; yi <= ub(x) - base; yi++) {
      if(lb(ys[yi]) > z_ub) {
        z_step = std::min(lb(ys[yi]), z_step);
        step_idxs.push(yi);
      } else
        EX_PUSH(expl, ys[yi] > z_ub);
    }
    if(step_idxs.size() > 0) {
      EX_PUSH(expl, z >= z_step);
      for(int yi : step_idxs)
        EX_PUSH(expl, ys[yi] < z_step);
    }
  }

  void push_hints(int low, int high, vec<clause_elt>& expl) {
    intvar::val_t z_ub = z.ub(s);

    intvar::val_t z_low = lb_0(z);
    intvar::val_t z_high = ub_0(z)+1;

    for(int ii : irange(low, high)) {
      intvar::val_t hint = cut_hint[ii];
      if(z_ub < hint) {
        assert(ys[ii].lb(s) >= hint);
        z_high = std::min(z_high, hint);
        expl.push(ys[ii] < hint);
      } else {
        assert(z.lb(s) >= hint);
        expl.push(ys[ii] >= hint);
        z_low = std::max(z_low, hint);
      }
    }
    expl.push(z < z_low);
    expl.push(z >= z_high);
  }
public:
  elem_var_bnd(solver_data* _s, intvar _z, intvar _x, vec<intvar>& _ys, int _base, patom_t _r)
    : propagator(_s), base(_base), x(_x), z(_z), ys(_ys), r(_r) {
    x.attach(E_LU, watch_callback(wake_default, this, 0, true));
    z.attach(E_LU, watch_callback(wake_default, this, 0, true));
    for(int ii : irange(ys.size())) {
      ys[ii].attach(E_LU, watch_callback(wake_default, this, ii, true)); 
      cut_hint.push(ys[ii].lb(s));
    }
    // Set initial bounds
    if(base > x.lb(s))
      set_lb(x,base, reason());
    if(base + ys.size() <= x.ub(s))
      set_ub(x,base + ys.size()-1, reason()); 
  }

  void root_simplify(void) {
    
  }

  bool check_sat(ctx_t& ctx) {
    for(int ii : irange(ys.size())) {
#if 1
      if(!x.in_domain_exhaustive(ctx, base + ii))
        continue;
#else
      if(x.lb(ctx) > ii + base || x.ub(ctx) < ii+base)
        continue;
#endif
      if(z.ub(ctx) < ys[ii].lb(ctx))
        continue;
      if(ys[ii].ub(ctx) < z.lb(ctx))
        continue;
      return true;
    }
    return false;
  }

  bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); }
    
   bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running elem_var_bnd]]" << std::endl;
#endif
       
      int_itv z_dom { z.lb(s), z.ub(s) };
      int_itv z_supp { z.ub(s)+1, z.lb(s)-1 };

      // Run forward, to find the lower bound
      int vi = x.lb(s) - base;
      int vend = x.ub(s) + 1 - base;

      for(; vi != vend; ++vi) {
        int_itv y_dom { ys[vi].lb(s), ys[vi].ub(s) };
        int_itv y_supp = z_dom & y_dom;
        if(y_supp.empty()) {
          cut_hint[vi] = std::max(z_dom.lb, y_dom.lb);
        } else {
          z_supp = y_supp;
          break;
        }
      }
      int low = vi;

      if(low + base > x.lb(s)) {
        if(!set_lb_with_eq(x,low + base, expl<&P::ex_x_lb>(lb(x)-base, expl_thunk::Ex_BTPRED)))
          return false;
      }

      int high = vi;
      for(++vi; vi != vend; ++vi) {
        int_itv y_dom { ys[vi].lb(s), ys[vi].ub(s) };
        int_itv y_supp = z_dom & y_dom;
        if(y_supp.empty()) {
          cut_hint[vi] = std::max(z_dom.lb, y_dom.lb);
        } else {
          z_supp |= y_supp;
          high = vi;
        }
      }
      if(high + base < x.ub(s)) {
        if(!set_ub_with_eq(x,high + base, expl<&P::ex_x_ub>(ub(x) - base, expl_thunk::Ex_BTPRED)))
          return false;
      }

      if(z_supp.lb > z.lb(s)) {
        if(!set_lb(z, z_supp.lb, expl<&P::ex_z_lb>(0, expl_thunk::Ex_BTPRED)))
          return false;
      }
      if(z_supp.ub < z.ub(s)) {
        if(!set_ub(z, z_supp.ub, expl<&P::ex_z_ub>(0, expl_thunk::Ex_BTPRED)))
          return false;
      }

      if(low == high) {
        intvar& y = ys[low];
        if(z_supp.lb > y.lb(s)) {
          if(!set_lb(y, z_supp.lb, expl<&P::ex_y_lb>(low, expl_thunk::Ex_BTPRED)))
            return false;
        }
        if(z_supp.ub < y.ub(s)) {
          if(!set_ub(y, z_supp.ub, expl<&P::ex_y_ub>(low, expl_thunk::Ex_BTPRED)))
           return false;
        }
      }

      return true;
    }

    int base;
    intvar x;
    intvar z;
    vec<intvar> ys;

    patom_t r;

    vec<intvar::val_t> cut_hint;
};

// Mixed propagator: domain consistent for x, but bounds-consistent for
// y and z.
#if 0
class elem_var_mix : public propagator, public prop_inst<elem_var_mix> {
  // Wakeup and explanation
  enum Task { Z_LB, Z_UB, Y_LB, Y_UB, SNUFF_LOW, SNUFF_HIGH, NOF_TASKS };

  inline int lub(void) const { return ub(lub_tree.root()); }
  inline int glb(void) const { return lb(glb_tree.root()); }

  watch_result wake_z_lb(int _z) {
    if(lb(z) > lub()) {
      // At least one index will be killed.
      queue_task(SNUFF_LOW);
    }
    return Wt_Keep;
  }
  watch_result wake_z_ub(int _z) {
    if(ub(z) < glb()) {
      // Some index is to be killed.
      queue_task(SNUFF_HIGH);
    }
    return Wt_Keep;
  }

  watch_result wake_y_lb(int yi) {
    if(!live_yi.elem(yi))
      return Wt_Keep;
    if(llb_tree.root() == yi) {
      if(llb_tree.repair_min(s)) {
        queue_task(Z_LB);
      }
    }
    repair_glb(yi);
    if(ub(z) < lb(ys[yi]))
      queue_task(SNUFF_HIGH);
    return Wt_Keep;
  }

  watch_result wake_y_ub(int yi) {
    if(!live_yi.elem(yi))
      return Wt_Keep;
    if(gub_tree.root() == yi) {
      if(gub_tree.repair_min(s)) {
        queue_task(Z_UB);
      }
    }
    repair_lub(yi);
    if(ub(ys[yi]) < lb(z))
      queue_task(SNUFF_LOW);
    return Wt_Keep;
  }

  watch_result wake_x(int _x, int k) {
    if(live_yi.elem(k)) {
      live_yi.remove(k);
      // Repair the trees 
      repair_glb(k);
      repair_lub(k);
      if(llb_tree.root() == k) {
        if(llb_tree.repair_min(s))
          queue_task(Z_LB);
      }
      if(gub_tree.root() == k) {
        if(gub_tree.repair_min(s))
          queue_task(Z_UB);
      }
    }
    return Wt_Keep;
  }

  void ex_y_lb(int yi, pval_t p, vec<clause_elt>& expl) {
    EX_PUSH(expl, x != yi);
    EX_PUSH(expl, z < ys[yi].lb_of_pval(p));
  }
  void ex_y_ub(int yi, pval_t p, vec<clause_elt>& expl) {
    EX_PUSH(expl, x != yi);
    EX_PUSH(expl, z > ys[yi].ub_of_pval(p));
  }

  /*
  void ex_x(int xi, pval_t _p, vec<clause_elt>& expl) {
    if(z.ub(s) < ys[xi].lb(s)) {
      expl.push(z > 
    }
  }
  */


  void cleanup(void) {
    tasks.clear();
    is_queued = false;
  }

  void ex_y_lb(int yi, pval_t p, vec<clause_elt>& expl) {
    expl.push(x != yi + base);
    expl.push(z < ys[yi].lb_of_pval(p));
  }

  void ex_y_ub(int yi, pval_t p, vec<clause_elt>& expl) {
    expl.push(x != yi+base);
    expl.push(z > ys[yi].ub_of_pval(p));
  }
   
  void ex_x(int yi, pval_t _p, vec<clause_elt>& expl) {
    if(ub(z) < supp[yi]) {
      expl.push(ys[yi] < supp[yi]);
      expl.push(z >= supp[yi]);
    } else {
      assert(supp[yi] < lb(z));
      assert(ub(ys[yi]) < lb(z));
      expl.push(ys[yi] > supp[yi]);
      expl.push(z <= supp[yi]);
    }
  }

  void ex_z_lb(int live_end, pval_t p, vec<clause_elt>& expl) {
    intvar::val_t z_lb = z.lb_of_pval(p);

    for(int ii : irange(live_end)) {
      int yi = live_yi[ii];
      expl.push(ys[yi] < z_lb);
    }

    if(live_end == 1) {
      expl.push(x != live_yi[0] + base);
    } else {
      for(int ii : irange(live_end, ys.size())) {
        int yi = live_yi[ii];
        expl.push(x == yi + base);
      }
    }
  }

  void ex_z_ub(int live_end, pval_t p, vec<clause_elt>& expl) {
    intvar::val_t z_ub = z.ub_of_pval(p);

    for(int ii : irange(live_end)) {
      int yi = live_yi[ii];
      expl.push(ys[yi] > z_ub);
    }

    if(live_end == 1) {
      expl.push(x != live_yi[0] + base);
    } else {
      for(int ii : irange(live_end, ys.size())) {
        int yi = live_yi[ii];
        expl.push(x == yi + base);
      }
    }
  }

public:
  elem_var_mix(solver_data* _s, intvar _z, intvar _x, vec<intvar>& _ys)
    : propagator(_s), x(_x), z(_z), ys(_ys),
      llb_tree(ys.size()), glb_tree(ys.size()),
      lub_tree(ys.size()), gub_tree(ys.size()),
      live_yi(ys.size()) {
    // Set all y-values as feasible
    live_yi.sz = ys.size();

    z.attach(E_LB, watch<&P::wake_z_lb>(0, Wt_IDEM));
    z.attach(E_UB, watch<&P::wake_z_ub>(0, Wt_IDEM));
    
    // Make sure all [x = k]s are available.
    make_eager(x);
    x.attach_rem(watch_val<&P::wake_x>(0, Wt_IDEM));

    // Attach on each of the ys. 
    for(int yi : irange(ys.size())) {
      if(!in_domain(x, yi)) {
        live_yi.remove(yi);
        continue;
      }
      if(ub(ys[yi]) < lb(z) || ub(z) < lb(ys[yi])) {
        if(!enqueue(*s, x != yi, reason()))
          throw RootFail();
        live_yi.remove(yi);
        continue;
      }
      ys[yi].attach(E_LB, watch<&P::wake_y_lb>(yi, Wt_IDEM));
      ys[yi].attach(E_UB, watch<&P::wake_y_ub>(yi, Wt_IDEM));
    }
  }

  void root_simplify(void) { }

   bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running elem_var_mix]]" << std::endl;
#endif

      for(int t : tasks) {
        switch(t) {
          Z_LB:
            {
              int yi = llb_tree.root();
              if(!set_lb(z, lb(ys[yi]), expl<&P::ex_z_lb>(0)))
                return false;
            }
            break;
          Z_UB:
            {
              int yi = gub_tree.root();
              if(!set_ub(z, ub(ys[yi]), expl<&P::ex_z_ub>(0)))
                return false;
            }
            break;
          Y_LB:
            {
              assert(live_yi.size() == 1);
              int yi = live_yi[0];
              if(!set_lb(ys[yi], lb(z), expl<&P::ex_y_lb>(yi)))
                return false;
            }
            break;
          Y_UB:
            {
              assert(live_yi.size() == 1);
              int yi = live_yi[0];
              if(!set_ub(ys[yi], ub(z), expl<&P::ex_y_ub>(yi)))
                return false;
            }
            break;
          SNUFF_LOW:
            { // Kill any indices with ub(y) < lb(z)
              if(!lub_tree.forall_lt([&](int yi) {
                if(!enqueue(*s, x != yi, expl<&P::ex_x_low>(yi)))
                  return false;
                  live_yi.remove(yi);
                }, lb(z)))
                return false;
            }
            break;
          SNUFF_HIGH:
            {
              if(!glb_tree.forall_lt([&](int yi) {
                if(!enqueue(*s, x != yi, expl<&P::ex_x_high>(yi)))
                  return false;
                live_yi.remove(yi);
              }, ub(z)))
                return false;
            }
            break;
          default:
            GEAS_ERROR;
        }
      }
      tasks.clear();

      return true;
   }

    intvar x;
    intvar z;
    vec<intvar> ys;

    struct MinLB {
      int operator()(solver_data* s, int yi) {
        if(!p->live_yi.elem(yi)) return INT_MAX;
        return ys[yi].lb(s);
      }
    };
    struct MinUB {
      int operator()(solver_data* s, int yi) {
        if(!p->live_yi.elem(yi)) return INT_MAX;
        return ys[yi].ub(s);
      }
    };
    struct MaxLB {
      int operator()(solver_data* s, int yi) {
        if(!p->live_yi.elem(yi)) return INT_MAX;
        return -ys[yi].lb(s);
      }
    };
    struct MaxUB {
      int operator()(solver_data* s, int yi) {
        if(!p->live_yi.elem(yi)) return INT_MAX;
        return -ys[yi].ub(s);
      }
    };

    // Track the least LB and greatest UB (of feasible
    // indices), to maintain supports for z bounds...
    weak_min_tree<int, EvalLLB> llb_tree;
    weak_min_tree<int, EvalGUB> gub_tree;

    // ...the next lower/upper bound thresholds
    // which will cause a variable will be killed...
    min_tree<int, EvalGLB> glb_tree;
    min_tree<int, EvalLUB> lub_tree;
    // ...and the set of surviving indices
    p_sparseset live_yi;

    // If x=k was removed, what value separated
    // ys[k] from z?
    vec<intvar::val_t> sep; 
};
#endif

// Non-incremental interval-based propagation
#if 0
class elem_var_simple : public propagator, public prop_inst<elem_var_simple> {
  // Wakeup and explanation
  static watch_result wake(void* ptr, int xi) {
    elem_var_simple* p(static_cast<elem_var_simple*>(ptr)); 
    p->queue_prop();
    return Wt_Keep;
  }

  // dom(z) inter dom(ys[i]) -> x != i.
  static void ex_x_ne_xi(void* ptr, int xi, pval_t pval, vec<clause_elt>& expl) {
    elem_var_simple* p(static_cast<elem_var_simple*>(ptr));
    
    intvar::val_t hint = p->cut_hint[xi];
    if(p->z.ub(p->s) < hint) {
      expl.push(p->z >= hint);
      expl.push(p->ys[xi] < hint);
    } else {
      expl.push(p->ys[xi] >= hint);
      expl.push(p->z < hint);
    }
  }

  static void ex_y_lb(elem_var_simple* p, int yi, intvar::val_t lb, vec<clause_elt>& expl) {
    expl.push(p->x != yi + p->base);
    expl.push(p->z < lb);
  }

  static void ex_y_ub(elem_var_simple* p, int yi, intvar::val_t ub, vec<clause_elt>& expl) {
    expl.push(p->x != yi + p->base);
    expl.push(p->z > ub);
  }

  static void ex_z_lb(P* p, int pos, intvar::val_t lb, vec<clause_elt>& expl) {
    GEAS_NOT_YET;
  }

  static void ex_z_ub(P* p, int pos, intvar::val_t lb, vec<clause_elt>& expl) {
    GEAS_NOT_YET;
  }

public:
  elem_var_simple(solver_data* _s, intvar _z, intvar _x, vec<intvar>& _ys, int _base, patom_t _r)
    : propagator(_s), base(_base), x(_x), z(_z), ys(_ys), r(_r) {
    // We assume the propagator is not half reified
    if(r != at_True) {
      GEAS_NOT_YET;
    }
     
    // Set initial explanation hints
    for(intvar& y : ys)
      cut_hint.push(y.lb(s));
  }

  void root_simplify(void) {
    
  }
    
   // FIXME
   /*
   forceinline indom(intvar& x, int k) {
     if(DOM) {
       return x.man->in_domain(x.idx, k);
     } else {
       return x.lb(s) <= k && k <= x.ub(s);
     }
   }
   */

   bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running elem_var_simple]]" << std::endl;
#endif
       
      int_itv z_dom { z.lb(s), z.ub(s) };
      int_itv z_supp { z.ub(s)+1, z.lb(s)-1 };

      // Run forward, collect supported tuples
      intvar* y = ys.begin();
      intvar* end = ys.end();
      int vv = base;

      for(; y != end; ++y, ++vv) {
        if(!in_domain(s, x, vv))
          continue;

        int_itv y_supp = z_dom & int_itv {(*y).lb(s), (*y).ub(s)};
        if(y_supp.empty()) {
          if(!enqueue(*s, x != vv, expl_thunk { ex_x_ne_xi, this, vv - base }))
            return false;
        } else {
          z_supp = y_supp;
          goto support_found;
        }
      }

      // No support, definitely false.
      // But should have failed earlier
      GEAS_ERROR;
      return false;

support_found:
      intvar* supp = y;
      for(++y, ++vv; y != end; ++y, ++vv) {
        int_itv y_supp = z_dom & int_itv {(*y).lb(s), (*y).ub(s)};
        if(y_supp.empty()) {
          if(!enqueue(*s, x != vv, expl_thunk { ex_x_ne_xi, this, vv - base }))
            return false;
        } else {
          z_supp |= y_supp;
          supp = end;
        }
      }

      if(z_supp.lb > z.lb(s)) {
        if(!set_lb(z, z_supp.lb, expl_thunk { ex_lb<ex_z_lb>, this, 0 }))
          return false;
      }

      if(z_supp.ub < z.ub(s)) {
        if(!set_ub(z, z_supp.ub, expl_thunk { ex_ub<ex_z_ub>, this, 1}))
          return false;
      }
       
      if(supp < end) {
        if(z_supp.lb > supp->lb(s)) {
          if(!set_lb(*supp, z_supp.lb, expl_thunk { ex_lb<ex_y_lb>, this, (int) (supp - ys.begin()), expl_thunk::Ex_BTPRED }))
            return false;
        }
        if(z_supp.ub < supp->ub(s)) {
          if(!set_ub(*supp, z_supp.ub, expl_thunk { ex_ub<ex_y_ub>, this, (int) (supp - ys.begin()), expl_thunk::Ex_BTPRED }))
            return false;
        }
      }
      return true;
    }

    // Constraint parameters
    int base;
    intvar x;
    intvar z;
    vec<intvar> ys;

    patom_t r;

    // Explanation hints
    vec<intvar::val_t> cut_hint;
};
#endif
int int_elem_bnd::prop_count = 0;

enum { ELEM_DOM_MAX = 50 };
// enum { ELEM_DOM_MAX = 20 };
// enum { ELEM_DOM_MAX = 0 };
bool int_element(solver_data* s, intvar z, intvar x, vec<int>& ys, patom_t r) {
#if 1
  if(ys.size() < ELEM_DOM_MAX) {
//    assert(s->state.is_entailed(r));
//    new int_elem_dom(s, x, ys, z-1);
//    return true;
    return int_element(s, r, z, x, ys, 1);
  } else {
    // new int_elem_bnd(s, r, z, x-1, ys);
    // return true;
    return int_elem_bnd::post(s, r, z, x-1, ys);
  }
#else
  return int_element(s, r, z, x, ys, 1);
#endif
}

bool elem_var_dom_dec(solver_data* s, intvar z, intvar x, vec<intvar>& ys) {
  // fprintf(stderr, "%%%% Decomposing var_int_element...\n");
  // Collect the supports for z values.
  for(int k : z.domain(s)) {
    if(!z.in_domain(s->state.p_vals, k))
      continue;

    vec<int> y_supps;
    for(int yi : irange(ys.size())) {
      if(!x.in_domain(s->state.p_vals, yi+1))
        continue;
      if(!ys[yi].in_domain(s->state.p_vals, k)) 
        continue;
      y_supps.push(yi);
    }
    if(y_supps.size() == 0) {
      if(!enqueue(*s, z != k, reason()))
        return false;
    } else if(y_supps.size() == 1) {
      int yi = y_supps[0];
      if(!add_clause(s, z != k, x == yi+1))
        return false;
      if(!add_clause(s, z != k, ys[yi] == k))
        return false;
    } else {
      vec<clause_elt> cl { z != k };
      for(int yi : y_supps) {
        patom_t at(new_bool(*s)); 
        add_clause(s, ~at, x == yi+1);
        add_clause(s, ~at, ys[yi] == k);
        add_clause(s, x != yi+1, ys[yi] != k, at);

        add_clause(s, ~at, z == k);
        cl.push(at);
      }
      if(!add_clause(*s, cl))
        return false;
    }
  }
  // Now collect supports for each index.
  for(int yi : irange(ys.size())) {
    if(!x.in_domain(s->state.p_vals, yi+1))
      continue;
    
    vec<int> y_supps;
    for(int k : z.domain(s)) {
      if(!z.in_domain(s->state.p_vals, k))
        continue;
      if(!ys[yi].in_domain(s->state.p_vals, k))
        continue; 
      y_supps.push(k);
    }
    if(y_supps.size() == 0) {
      if(!enqueue(*s, x != yi+1, reason()))
        return false;
    } else if(y_supps.size() == 1) {
      int k = y_supps[0];
      if(!add_clause(s, x != yi+1, z == k))
        return false;
      if(!add_clause(s, x != yi+1, ys[yi] == k))
        return false;
    } else {
      vec<clause_elt> cl { x != yi+1 };
      for(int k : y_supps) {
        patom_t at(new_bool(*s));
        add_clause(s, ~at, z == k);
        add_clause(s, ~at, ys[yi] == k);
        add_clause(s, at, z != k, ys[yi] != k);

        cl.push(at);
      }
      if(!add_clause(*s, cl))
        return false;
    }
  }
  return true;
}
bool var_int_element(solver_data* s, intvar z, intvar x, vec<intvar>& ys, patom_t r) {
  // new elem_var_bnd(s, z, x, ys, 1, r);
  // return true; 
#if 0
  if(z.dom_sz_exact(s->state.p_vals) <= 2 * ys.size()) {
    assert(s->state.is_entailed(r));
    return elem_var_dom_dec(s, z, x, ys);
  } else {
    return elem_var_bnd::post(s, z, x, ys, 1, r);
  }
#else
  return elem_var_bnd::post(s, z, x, ys, 1, r);
#endif
}
}
