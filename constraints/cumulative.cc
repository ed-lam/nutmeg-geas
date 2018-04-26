#include <algorithm>
#include "solver/solver_data.h"
#include "engine/propagator.h"
#include "engine/propagator_ext.h"
#include "constraints/builtins.h"

#include "mtl/bool-set.h"
#include "mtl/p-sparse-set.h"

namespace geas {

// Totally non-incremental time-table propagator.
// ============================================

typedef unsigned int task_id;

enum evt_kind { ET = 0, ST = 1};
/*
struct pevt {
  pevt_kind k;
  task_id task;
  int time;
  int cap;
};

*/

// V is the type of resource consumption.
template <class V>
class cumul {
public:
  class cumul_val : public propagator, public prop_inst<cumul_val> {
    typedef prop_inst<cumul_val> I;
    typedef cumul_val P;

    // Typedefs
    typedef unsigned int task_id;
    typedef trailed<V> TrV;
    struct task_info {
      intvar s;
      int d;
      V r;
    };

    struct evt_info {
      evt_kind kind;  
      task_id task;
      int t;
      V level;
    };

    struct ex_info {
      task_id t;
      int ex_time;
    };

    struct {
      bool operator()(const evt_info& x, const evt_info& y) const {
        if(x.t == y.t) {
          // Process ends before starts.
          return x.kind < y.kind;
        }
        return x.t < y.t;
      }
    } pevt_cmp;

    // Parameters
    vec<task_info> tasks; // We order tasks by decreasing r.
    V cap; // Maximum resource capacity

    // Persistent state
    Tint active_end;

    p_sparseset profile_tasks;
    p_sparseset active_tasks;

    vec<ex_info> exs;
    char exs_saved;

    // Transient state.
    vec<evt_info> profile;
    boolset lb_change;
    boolset ub_change;
    bool profile_changed;

    // Helper functions
    inline int est(int xi) const { return lb(tasks[xi].s); }
    inline int eet(int xi) const { return lb(tasks[xi].s) + tasks[xi].d; }
    inline int lst(int xi) const { return ub(tasks[xi].s); }
    inline int let(int xi) const { return ub(tasks[xi].s) + tasks[xi].d; }

    inline V mreq(int xi) const { return tasks[xi].r; }
    inline int dur(int xi) const { return tasks[xi].d; }

    int make_ex(task_id t, int time) {
      this->template save(exs._size(), exs_saved);
      int id = exs.size();
      exs.push(ex_info { t, time });
      return id;
    }

    watch_result wake_lb(int ti) {
      if(profile_tasks.elem(ti)) {
        profile_changed = true;
        queue_prop();
      } else {
        if(lst(ti) < eet(ti)) {
          trail_push(s->persist, profile_tasks.sz);
          profile_tasks.insert(ti);
          profile_changed = true;
          queue_prop();
        } else if(active_tasks.elem(ti)) {
          lb_change.add(ti);
          queue_prop();
        }
      }
      return Wt_Keep;
    }

    watch_result wake_ub(int ti) {
      if(profile_tasks.elem(ti)) {
        profile_changed = true;
        queue_prop();
      } else {
        if(lst(ti) < eet(ti)) {
          trail_push(s->persist, profile_tasks.sz);
          profile_tasks.insert(ti);
          profile_changed = true;
          queue_prop();
        } else if(active_tasks.elem(ti)) {
          ub_change.add(ti);
          queue_prop();
        }
      }
      return Wt_Keep;
    }

    void log_ptasks(void) {
      std::cerr << "{";
      for(task_id ti : profile_tasks) {
        std::cerr << ti << ":[" << lst(ti) << "," << eet(ti) << ")|"
          << mreq(ti) << " ";
      }
      std::cerr << "}" << std::endl;
    }

    void log_profile(void) {
      for(evt_info e : profile) {
        std::cerr << e.t << ":" << e.task << ":" << (e.kind == ST ? "+" : "-") << e.level << " ";
      }
      std::cerr << std::endl;
    }

    bool rebuild_profile(vec<clause_elt>& confl) {
#ifdef LOG_PROFILE
      std::cout << "Building profile." << std::endl << "-------------------" << std::endl;
      log_ptasks();
#endif

      profile.clear();
      for(task_id ti : profile_tasks) {
        profile.push(evt_info { ST, ti, lst(ti), mreq(ti) });
        profile.push(evt_info { ET, ti, eet(ti), mreq(ti) });
      }
      std::sort(profile.begin(), profile.end(), pevt_cmp);

      // Now replace the deltas with actual values

#ifdef LOG_PROFILE
      log_profile();
#endif

      V cumul(0);
      V p_max(0);
      for(evt_info& e : profile) {
        if(e.kind == ST) {
          cumul += e.level;
          if(cumul > p_max) {
            if(cumul > cap) {
              explain_overload(e.t, confl);
              return false;
            }
            p_max = cumul;
          }
        } else {
          cumul -= e.level;
        }
        e.level = cumul;
      }

#ifdef LOG_PROFILE
      log_profile();
      std::cerr << std::endl;
#endif

      // Activate any remaining tasks which might
      // be shifted.
      V req_max(cap - p_max);
      int ti = active_end;
      if(ti < tasks.size() && mreq(ti) > req_max) {
        trail_push(s->persist, active_tasks.sz);
        active_tasks.insert(ti);
        for(++ti; ti < tasks.size(); ++ti) {
          if(mreq(ti) <= req_max)
            break;
          active_tasks.insert(ti);
        }
        set(active_end, ti);
      }
      return true;
    }

    bool sweep_fwd(task_id ti) {
      // Find the starting interval
      const task_info& t(tasks[ti]);

      evt_info* s = std::upper_bound(profile.begin(), profile.end(),
        est(ti), [](const int& t, const evt_info& e /*, const int& t*/) { return e.t + (e.kind == ST) < t; });
      if(s == profile.end())
        return true;
      // Task stats in the previous interval   
      V lev_max = cap - mreq(ti);

      int end_time = est(ti) + t.d;
      if(s[-1].task == ti)
        return true;
      int ex_time = s[-1].t;
      V seg_level = s[-1].level;

      while(s->t < end_time) {
        if(seg_level > lev_max) {
          // Shift start and reset.
          if(!set_lb(t.s, s->t, this->template expl<&P::ex_est>(make_ex(ti, ex_time), expl_thunk::Ex_BTPRED)))
            return false;
          end_time = s->t + t.d;
        }
        // The profile's going to be updated anyway.
        if(s->task == ti)
          return true;
        ex_time = s->t;
        seg_level = s->level;
        ++s;
      }
      return true;
    }

    inline void EX_PUSH(vec<clause_elt>& expl, patom_t at) {
      assert(!ub(at));
      expl.push(at);
    }

    void ex_est(int ex_id, pval_t p, vec<clause_elt>& expl) {
      ex_info e(exs[ex_id]);
      task_id ti(e.t);
      const task_info& t(tasks[ti]);
      int t_est(std::max(t.s.lb_of_pval(p), e.ex_time+1));
      // int t_est(std::max(t.s.lb_of_pval(p), e.ex_time+1));

      // Assumption: we're doing stepwise-propagation.
      // So at this point, lb(t.s) < est, and every task
      // active at (est-1) was active from lb(t.s) + dur - 1.
      
      // So, we collect a sufficient set of tasks, active at
      // (est-1).
      V e_req = (cap - t.r);
      vec<task_id> etasks;
      for(task_id p : profile_tasks) {
        if(lst(p) <= e.ex_time && e.ex_time < eet(p)) {
          assert(p != ti);
          // assert(lst(p) >= lb(t.s));

          etasks.push(p);
          if(e_req < mreq(p)) {
            // Found a cover. Minimize, and find a relaxed
            // lb for t.
            V slack = mreq(p) - e_req;
            
            int jj = 0;
            for(int ii = 0; ii < etasks.size(); ++ii) {
              if(mreq(p) < slack) {
                slack -= mreq(p);
                continue;
              }
              etasks[jj++] = etasks[ii];
            }
            etasks.shrink_(etasks.size() - jj);
            // Now construct the actual explanation
            // Either t is entirely before earliest...
#if 1
            // EX_PUSH(expl, t.s <= e.ex_time - t.d);
            // EX_PUSH(expl, t.s < lb(t.s));
            // ...or some member of etasks doesn't cover.
            for(task_id p : etasks) {
              EX_PUSH(expl, tasks[p].s > e.ex_time);
              // FIXME: Probably an off-by-one here.
              EX_PUSH(expl, tasks[p].s < t_est - tasks[p].d);
            }
#else
            // Semi-naive explanation
            expl.push(t.s < lb(t.s));
            for(task_id p : etasks) {
              expl.push(tasks[p].s < lb(tasks[p].s));
              expl.push(tasks[p].s > ub(tasks[p].s));
            }
#endif
            return;
          }
          e_req -= mreq(p);
        }
      }
      // Should be unreachable
      ERROR;
    }

    void explain_overload(int t, vec<clause_elt>& confl) {
      // Usual trick: collect a sufficient set of tasks, then
      // discard until we have a minimal set.
      vec<task_id> e_tasks;
      V to_cover(cap);
      for(task_id p : profile_tasks) {
        if(lst(p) <= t && t < eet(p)) {
          e_tasks.push(p);
          if(to_cover < mreq(p)) {
            // Found a sufficient cover.
            V slack(mreq(p) - to_cover);
            for(task_id q : e_tasks) {
              // Can be omitted; we have sufficient
              // slack later on.
              if(mreq(q) < slack) {
                slack -= mreq(q);
                continue;
              }
              confl.push(tasks[q].s <= t - tasks[q].d);
              confl.push(tasks[q].s > t);
            }
            return;
          }
          to_cover -= mreq(p);
        }
      }
      ERROR;
    }

  public:
    cumul_val(solver_data* s, vec<intvar>& starts, vec<int>& dur, vec<V>& res, V _cap)
      : propagator(s), cap(_cap)
      , active_end(0)
      , profile_tasks(starts.size())
      , active_tasks(starts.size())
      , lb_change(starts.size())
      , ub_change(starts.size())
      , profile_changed(false) {
      for(int xi: irange(starts.size())) {
        task_info t(task_info { starts[xi], dur[xi], res[xi] });
        t.s.attach(E_LB, this->template watch<&P::wake_lb>(xi));
        t.s.attach(E_UB, this->template watch<&P::wake_ub>(xi));
        tasks.push(t);
        if(lst(xi) < eet(xi)) {
          profile_tasks.insert(xi);
          profile_changed = true;
        }
      }
    }

    bool propagate(vec<clause_elt>& confl) {
      if(profile_changed) {
        if(!rebuild_profile(confl))
          return false;
        
#if 0
        for(task_id t : active_tasks) {
          if(!sweep_fwd(t))
            return false;
          // if(!sweep_bwd(t))
          //   return false;   
        }
#endif
      } else {
        // If the profile hasn't changed, only sweep
        // variables with updated bounds.
#if 0
        for(task_id t : lb_change) {
          if(!sweep_fwd(t))
            return false;
        }
        /*
        for(task_id t : ub_change) {
          if(!sweep_bwd(t))
            return false;
        }
        */
#endif
      }
      return true;
    }

    void cleanup(void) {
      lb_change.clear();
      ub_change.clear();
      profile_changed = false;
      is_queued = false;
    }
  };
};

bool cumulative(solver_data* s,
  vec<intvar>& starts, vec<int>& duration, vec<int>& resource, int cap) {
  // new cumul_prop(s, starts, duration, resource, cap);
  // return true;
  return cumul<int>::cumul_val::post(s, starts, duration, resource, cap);
  // assert(0);
  // return false;
}

}
