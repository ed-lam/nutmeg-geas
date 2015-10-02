// Wrapper for conflict analysis.
#include "engine/conflict.h"

// Add a atom to the current resolution state.
void conflict_state::add_atom(env* e, atom l)
{
  AtomManager* man(e->atom_man(l));
  man->add_conflict_atom(e->to_atom_(l)); 
  seen[l.id] = true;
//  assert(0 && "add_atom not yet impatomented.");
}

// Update a the conflict state with an inference.
bool conflict_state::update_resolvent(env* e, atom_inf& inf, vec<atom>& learnt_out)
{
  atom l(inf.l);
  if(!seen[l.id])
    return false;

  // Ask the manager how to update the table.
  // May cause side-effects if the manager is
  // abusing the meaning of data[idx].
  AtomManager* man(e->atom_man(l));
  atom_tok tok(e->atid_info[l.id].ref);
  ResolvableT r(man->is_resolvable(tok, l.info, e->conflict_cookie[l.id]));
  if(r == R_NotResolvable)
    return false;

  // Either way, the atom has been resolved, and
  // is at the current level.
  count--;

  // If this is the last thing at the
  // current decision level, stop here
  // instead of continuing to resolve.
  if(count == 0)
  {
    learnt_out.push(l);
      
    return true;
  }

  // Shouldn't be resolving a decision literal.
  expln ex(inf.ex);
  assert(ex.kind != Ex_Dec);
  if(ex.kind == Ex_Cl)
  {
    assert(0 && "Special-case resolution for clauses not implemented.");
    // An existing clause. l should be the 0th element.
    /*
    clause* cl(ex.cl);
    
    // Add all the other elements.
    for(int li = 1; li < cl->sz; cl++)
      add_atom(e, e->atom_of_lit(cl->ls[li]));
      */
  } else {
    // It's a thunk.
    ex_thunk et(ex.ex); 

    // Get the explanation.
    vec<atom> expln;
    et.fun(et.data, et.cookie, expln);
    
    // Add each eatoment in the explanation
    for(int li = 0; li < expln.size(); li++)
      add_atom(e, expln[li]);
  }
  return false;
}

void conflict_state::analyze_conflict(env* e, vec<atom>& confl, vec<atom>& out_learnt)
{
  assert(0 && "conflict_state::analyze_conflict not implemented.");
  /*
  conflict_state.clear();

  for(atom at : confl)
    conflict_state.add_atom(e, at);
  
  size_t idx = atom_trail.size();
  while(conflict_state.curr_level_count() > 1)
  {
    atom_inf inf = e->atom_trail[--idx];
    if(conflict_state.must_resolve(inf))
      conflict_state.resolve(inf);
    e->atom_trail.pop();
  }

  conflict_state.retrieve_learnt(out_learnt);
  */
}
