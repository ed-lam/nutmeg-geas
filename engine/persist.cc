#include <stdint.h>
#include "utils/defs.h"
#include "engine/phage-types.h"
#include "solver/solver_data.h"
#include "engine/persist.h"

namespace phage {

void push_level(solver_data* s) {
  persistence& p(s->persist);

  s->infer.trail_lim.push(s->infer.trail.size());

  p.bvar_trail_lim.push(p.bvar_trail.size());
  p.dtrail_lim.push(p.data_trail.size());

  for(pid_t pi : p.touched_preds) {
    p.pred_touched[pi] = false;
    persistence::pred_entry e = { pi, s->state.p_last[pi] };
    p.pred_ltrail.push(e);
  }
  p.pred_ltrail_lim.push(p.pred_ltrail.size());
  p.touched_preds.clear();
}

// Doesn't call destructors
template<class T>
inline void dropTo_(vec<T>& v, int sz) {
  v.shrink_(v.size() - sz);
}

inline void restore_data_elt(solver_data* s, persistence::data_entry e) {
  switch(e.sz) {
    case 1:
      *((uint8_t*) e.ptr) = ((uint8_t) e.val);
      break;
    case 2:
      *((uint16_t*) e.ptr) = ((uint16_t) e.val);
      break;
    case 4:
      *((uint32_t*) e.ptr) = ((uint32_t) e.val); 
      break;
    default:
      *((uint64_t*) e.ptr) = ((uint64_t) e.val);
  }
}

inline void bt_data(solver_data* s, unsigned int l) {
  persistence& p(s->persist);
  assert(l < p.dtrail_lim.size());

  unsigned int p_lim = p.dtrail_lim[l];
  for(auto e : rev_range(&p.data_trail[p_lim], p.data_trail.end()))
    restore_data_elt(s, e);
  dropTo_(p.data_trail, p_lim);
  dropTo_(p.dtrail_lim, l);
}

inline void bt_explns(solver_data* s, unsigned int l) {
  NOT_YET_WARN;
}

inline void bt_preds(solver_data* s, unsigned int l) {
  pred_state& st(s->state);
  persistence& p(s->persist);
  infer_info& inf(s->infer);

  // Don't use the implication graph for restoration;
  // use pred_ltrail instead.
  assert(l < inf.trail_lim.size());
  dropTo_(inf.trail, inf.trail_lim[l]);
  dropTo_(inf.trail_lim, l);
  
  // Restore Booleans
  int blim = p.bvar_trail_lim[l];
  for(int b : range(&p.bvar_trail[blim], p.bvar_trail.end()))
    st.b_assigns[b] = l_Undef.to_int();
  dropTo_(p.bvar_trail, blim);
  dropTo_(p.bvar_trail_lim, l);

  assert(l < p.pred_ltrail_lim.size());
  // Reset preds touched at the current level
  for(pid_t pi : p.touched_preds) {
    p.pred_touched[pi] = false;
    st.p_vals[pi] = st.p_last[pi];
  }
  p.touched_preds.clear();

  // Now walk through the history, walking back p_vals
  // and p_last in lockstep.
  int p_lim = p.pred_ltrail_lim[l];
  for(auto e : rev_range(&p.pred_ltrail[p_lim], p.pred_ltrail.end())) {
    st.p_vals[e.p] = st.p_last[e.p];
    st.p_last[e.p] = e.v;
  }
  dropTo_(p.pred_ltrail, p_lim);
  dropTo_(p.pred_ltrail_lim, l);
}

void bt_to_level(solver_data* s, unsigned int l) {
  // Three components of state:
  // predicates, explanations, and opaque data

  // Deal with current and last-level pred values
  bt_preds(s, l);

  // Restore other assorted data
  bt_data(s, l);

  // Collect temporary explanations
  bt_explns(s, l); 
}

}
