// Switch to more efficient representation.
#include <map>

#include "engine/env.h"
#include "engine/trail.h"
#include "vars/intvar.h"

class IMan_lazy : public IVarManager {
  typedef Watcher::Info atom_watch;
  typedef WatcherT<char>::Info evt_watch;

  typedef std::map<int, atom_watch> atwatch_map; 

  class IVar_impl {
  public:
    IVar_impl(env* e, int min, int max)
      : lb(&(e->gen_trail), min), ub(&(e->gen_trail), max)
    { }

    IVar_impl& operator=(const IVar_impl& v)
    {
      lb = v.lb;
      ub = v.ub;
      return *this;
    }

    TrInt lb;    
    TrInt ub;
  };
public:
  IMan_lazy(env* e)
    : IVarManager(e)
  { } 
  
  // General Atom-management stuff.
  void attach(_atom x, Watcher* w, int k)
  {
    int xi = x.tok>>2; 
    int val = x.info;

    switch(x.tok&3)
    {
      case 0: // x <= val
        ub_atmap[xi].insert(std::make_pair(val, Watcher::Info(w, k)));
        break;

      case 1: // x > val
        lb_atmap[xi].insert(std::make_pair(val+1, Watcher::Info(w, k)));
        break;

      case 2: // x = val
        eq_atmap[xi].insert(std::make_pair(val, Watcher::Info(w, k)));
        break;

      case 3: // x != val
        neq_atmap[xi].insert(std::make_pair(val, Watcher::Info(w, k)));
        break;

      default:
        assert(0 && "Not reachable.");
    }
  }

  // Mark a atom as no longer persistent
  void unbind(_atom x) { }

  // Attach an event 
  // virtual void watch(atom_id id, watch_thunk& c) = 0;

  // Assert an atom
  // Pre: value(x) != l_False.
  bool post(_atom at)
  {
    int xi = at.tok>>2;
    int val = at.info;

    switch(at.tok&3)
    {
      case 0: // x <= val
        printf("  posting v%d <= %d\n", xi, val);
        return set_ub(xi, val);

      case 1: // x > val
        printf("  posting v%d > %d\n", xi, val);
        return set_lb(xi, val+1);

      case 2: // x = val
        printf("  posting v%d = %d\n", xi, val);
        return set_val(xi, val);

      case 3: // x != val
        printf("  posting v%d != %d\n", xi, val);
        return rem_val(xi, val);

      default:
        assert(0 && "Not reachable.");
        return false;
    }
  }

  bool set_ub(int xi, int val)
  {
    IVar_impl& x(*ivars[xi]);

    int lb = x.lb.val();
    if(lb > val)
      return false;

    char evt = IVE_UB;
    if(lb == val)
      evt |= IVE_FIX;

    // Update the bounds
    int old_ub = x.ub.val();
    x.ub = val;

    // Call general watchers
    for(evt_watch& w : ub_watchers[xi])
      w(evt);

    if(lb == val)
    {
      for(evt_watch& w : fix_watchers[xi])
        w(evt);
    }

    // Call atom watchers
    atwatch_map& atmap(ub_atmap[xi]);
    auto at_low(atmap.lower_bound(val));
    auto at_high(atmap.upper_bound(old_ub));

    for(; at_low != at_high; --at_high)
      (*at_high).second();

    return true;
  }

  bool set_lb(int xi, int val)
  {
    IVar_impl& x(*ivars[xi]);

    int ub = x.ub.val();
    if(ub < val)
      return false;

    char evt = IVE_UB;
    if(ub == val)
      evt |= IVE_FIX;

    // Update the bounds
    int old_lb = x.lb.val();
    x.lb = val;

    // Call general watchers
    for(evt_watch& w : lb_watchers[xi])
      w(evt);

    if(ub == val)
    {
      for(evt_watch& w : fix_watchers[xi])
        w(evt);
    }

    // Call atom watchers
    atwatch_map& atmap(lb_atmap[xi]);
    auto at_low(atmap.lower_bound(old_lb));
    auto at_high(atmap.upper_bound(val));

    for(; at_low != at_high; ++at_low)
      (*at_low).second();

    return true;

    return false;
  }

  bool set_val(int xi, int val)
  {
    // FIXME
    return false;
  }

  bool rem_val(int xi, int val)
  {
    // FIXME
    return false;
  }

  // Can we do this more cheaply?
  // virtual lit undo(_atom& x) = 0;

  // Evaluate a atom under the current state.
  // Not super compact.
  lbool value(_atom at) {
    // Determine the variable id.
    int x = at.tok>>2;
    // And the value
    int val = at.info;

    // Determine the kind of atom
    IVar_impl& x_impl(*ivars[x]);

    int lb = x_impl.lb.val();
    int ub = x_impl.ub.val();
    // Determine the kind of literal
    switch(at.tok&3)
    {
      case 0: // x <= val
      {
        if(ub <= val)
          return l_True;
        if(lb > val)
          return l_False;
        return l_Undef;
      }
      case 1: // x > val
      {
        if(ub <= val)
          return l_False;
        if(lb > val)
          return l_True;
        return l_Undef;
      }
      case 2: // x = val
      {
        if(lb == val && ub == val)
          return l_True;
        if(ub < val)
          return l_False;
        if(lb > val)
          return l_False;
        return l_Undef;
      }
      case 3: // x != val
      {
        if(lb == val && ub == val)
          return l_False;
        if(ub < val)
          return l_True;
        if(lb > val)
          return l_False;
        return l_Undef;
      }
      default:
        assert(0 && "Unreachable.");
        return l_Undef;
    }
  }

  int false_level(_atom x)
  {
    assert(0 && "IVarMan::false_level not yet implemented.");
    return 0;
  }

  // x -> y?
  bool le(_atom x, _atom y) {
    assert(0 && "Not implemented.");
    return false;
  }

  // Are all variables managed by this fixed?
  bool is_fixed(void) {
    for(IVar_impl* v : ivars)
    {
      if(v->lb.val() != v->ub.val())
        return false;
    }
    return true;
  }

  // Choose a branch literal. Extend to handle
  // branches later.
  atom branch(void) {
    // Pick a variable that isn't fixed.
    printf("Selecting branch.\n");
    for(int vi = 0; vi < ivars.size(); vi++)
    {
      printf("  trying v%d.\n", vi);
      IVar_impl& v(*ivars[vi]);
      if(v.lb.val() != v.ub.val())
      {
        // Pick an atom
        printf("  branching on [v%d <= %d].\n", vi, v.lb.val());
        return le_atom(vi, v.lb.val());
      }
    }
    return atom_undef();
  }

  // Conflict clause resolution
  ResolvableT is_resolvable(atom_id id, atom_val val, atom_val prev) {
    assert(0 && "Not implemented.");
    return R_NotResolvable;  
  }

  void collect(atom_id id, atom_val v, vec<atom>& learnt_out) {

  }

  // Specific IntVar methods
  IntVar newVar(int lb, int ub) {
    std::cout << e << std::endl;

    int id = ivars.size();
    atom_tok at_tok = new_atom_tok();
    new_atom_tok(); // eq_atom
    assert(at_tok == 2*id);

    ivars.push(new IVar_impl(e, lb, ub));
    lb_watchers.push();
    ub_watchers.push();
    fix_watchers.push();

    lb_atmap.push();
    ub_atmap.push();
    eq_atmap.push();
    neq_atmap.push();

    return IntVar(this, id);
  }

  void add_watch(ivar_id id, WatcherT<char>* w,
    int ref, char events)
  {
    if(events & IVE_LB)
      lb_watchers[id].push(evt_watch(w, ref));
    if(events & IVE_UB)
      ub_watchers[id].push(evt_watch(w, ref));
    if(events & IVE_FIX)
      fix_watchers[id].push(evt_watch(w, ref));
  }

  // TrInt can be casted implicitly to int.
  int lb(ivar_id id) { return ivars[id]->lb; }
  int ub(ivar_id id) { return ivars[id]->ub; }
  bool indom(ivar_id id, int k) {
    return ivars[id]->lb <= k && k <= ivars[id]->ub;
  }

  atom le_atom(ivar_id id, int k) {
    return mk_atom(tok_ids[2*id]<<1, k);
  }
  atom eq_atom(ivar_id id, int k) {
    return mk_atom((tok_ids[2*id+1]<<1), k);
  }

protected:
  vec<IVar_impl*> ivars;

  // Ugh, ugly.
  vec< vec<evt_watch> > lb_watchers;
  vec< vec<evt_watch> > ub_watchers;
  vec< vec<evt_watch> > fix_watchers;

  vec<atwatch_map> lb_atmap;
  vec<atwatch_map> ub_atmap;
  vec<atwatch_map> eq_atmap;
  vec<atwatch_map> neq_atmap;
};

IVarManager* newIVarMan(env* e, IManKind kind)
{
  assert(kind == IV_Lazy);
  return new IMan_lazy(e);
}
