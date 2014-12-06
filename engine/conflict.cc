// Wrapper for conflict analysis.
#include "engine/clause.h"
#include "engine/conflict.h"

// Add a atom to the current resolution state.
void conflict_state::add_atom(atom l)
{
//  AtomManager* man(e->managers[l.kind]); 
  assert(0 && "add_atom not yet impatomented.");
}

// Update a the conflict state with an inference.
bool conflict_state::update(atom_inf& inf, vec<atom>& learnt_out)
{
  atom l(inf.l);
  atom_sig sig(l.kind, l.data.id);
  atom_table::iterator it(tab.find(sig));

  // Definitely not in the conflict clause.
  if(it == tab.end())
    return false;

  // Ask the manager how to update the table.
  // May cause side-effects if the manager is
  // abusing the meaning of data[idx].
  int idx = (*it).second;
  AtomManager* man(e->managers[l.kind]);
  ResolvableT r(man->is_resolvable(l.data.id, l.data.info, data[idx]));
  if(r == R_NotResolvable)
    return false;

  // Entry is to be erased from the table.
  if(r == R_ResolveElim)
    tab.erase(it);

  // Either way, the atom has been resolved, and
  // is at the current level.
  count--;

  // If this is the last thing at the
  // current decision level, top here
  // instead of 
  if(count == 0)
  {
    learnt_out.clear();
    learnt_out.push(l);
    
    atom_table::iterator it(tab.begin());

    // Now ask the relevant managers
    // for the remainder of the learnt clause.
    for(; it != tab.end(); ++it)
    {
      atom_sig sig((*it).first);
      int idx = (*it).second;
      AtomManager* lman(e->managers[sig.kind]);
      lman->collect(sig.id, data[idx], learnt_out);
    }
     
    return true;
  }

  // Shouldn't be resolving a decision literal.
  expln ex(inf.ex);
  assert(ex.kind != Ex_Dec);
  if(ex.kind == Ex_Cl)
  {
    // An existing clause. l should be the 0th eatoment.
    clause* cl(ex.cl);
    
    // Add all the other eatoments.
    for(int li = 1; li < cl->sz; cl++)
      add_atom(e->atom_of_lit(cl->ls[li]));
  } else {
    // It's a thunk.
    ex_thunk et(ex.ex); 

    // Get the explanation.
    vec<atom> expln;
    et.fun(et.data, et.cookie, expln);
    
    // Add each eatoment in the explanation
    for(int li = 0; li < expln.size(); li++)
      add_atom(expln[li]);
  }
  return false;
}
