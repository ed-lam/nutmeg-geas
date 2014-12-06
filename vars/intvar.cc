#include "engine/env.h"
#include "engine/vTrail.h"
#include "vars/intvar.h"

class IMan_lazy : public IVarManager {
  class IVar_impl {
  public:
    IVar_impl(env* e, int min, int max)
      : lb(&(e->gen_vtrail), min), ub(&(e->gen_vtrail), max)
    { }

    IVar_impl& operator=(const IVar_impl& v)
    {
      lb = v.lb;
      ub = v.ub;
      return *this;
    }

    VTrail::TrInt lb;    
    VTrail::TrInt ub;
  };
public:
  IMan_lazy(env* e)
    : IVarManager(e)
  { } 

  
  // General Atom-management stuff.
  lit bind(_atom& x)
  {
    assert(0 && "Not implemented.");
    return mk_lit(-1, 1);
  }

  // Mark a atom as no longer persistent
  void unbind(_atom& x) { }

  // Attach an event 
  // virtual void watch(atom_id id, watch_thunk& c) = 0;

  // Assert an atom
  bool post(_atom& x, vec<atom>& out_confl) 
  {
    assert(0 && "Not implemented.");
    return true;
  }
  // Can we do this more cheaply?
  // virtual lit undo(_atom& x) = 0;

  // Evaluate a atom under the current state.
  lbool value(_atom& x) {
    assert(0 && "Not implemented.");
    return l_Undef; 
  }

  // x -> y?
  bool le(_atom& x, _atom& y) {
    assert(0 && "Not implemented.");
    return false;
  }

  // Are all variables managed by this fixed?
  bool is_fixed(void) {
    for(int ii = 0; ii < ivars.size(); ii++)
    {
      if(ivars[ii].lb.val() != ivars[ii].ub.val())
        return false;
    }
    return true;
  }

  // Choose a branch literal. Extend to handle
  // branches later.
  atom branch(void) {
    // FIXME: IMPLEMENT
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
    assert(0 && "Not implemented.");     
    int id = ivars.size();
    ivars.push(IVar_impl(e, lb, ub));
    return IntVar(this, id);
  }

  void add_watch(ivar_id id, int events,
    Propagator* p, int ref)
  {
    
  }

  // TrInt can be casted implicitly to int.
  int lb(ivar_id id) { return ivars[id].lb; }
  int ub(ivar_id id) { return ivars[id].ub; }
  bool indom(ivar_id id, int k) {
    return ivars[id].lb <= k && k <= ivars[id].ub;
  }

  atom le_atom(ivar_id id, int k) = 0;
  atom eq_atom(ivar_id id, int k) = 0;

protected:
  vec<IVar_impl> ivars;
};

