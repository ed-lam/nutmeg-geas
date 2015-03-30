// Wrapper for conflict analysis.
#include "engine/conflict.h"

// Add a atom to the current resolution state.
void conflict_state::add_atom(env* e, atom l)
{
//  AtomManager* man(e->managers[l.kind]); 
  assert(0 && "add_atom not yet impatomented.");
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
  // current decision level, top here
  // instead of 
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
    // An existing clause. l should be the 0th element.
    /*
    clause* cl(ex.cl);
    
    // Add all the other eatoments.
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
  /*
  conflict_state cstate(e);
  for(int li = 0; li < confl.size(); li++)
    cstate.add_atom(confl[li]);
    */

  atom_inf inf(e->atom_trail.last());
  while(!update_resolvent(e, inf, out_learnt))
  {
    // Handle backtracking somewhere.
    e->atom_trail.pop();
    inf = e->atom_trail.last();
  }
  // conflict_state::update should have left the 1-UIP clause in out_learnt.
  return;
}
