// Wrapper for conflict analysis.
#include "engine/clause.h"
#include "engine/conflict.h"

// Add a lemma to the current resolution state.
void conflict_state::add_lemma(lemma l)
{
//  LemmaManager* man(e->managers[l.kind]); 
  assert(0 && "add_lemma not yet implemented.");
}

// Update a the conflict state with an inference.
bool conflict_state::update(lem_inf& inf, vec<lemma>& learnt_out)
{
  lemma l(inf.l);
  lem_sig sig(l.kind, l.data.id);
  lem_table::iterator it(tab.find(sig));

  // Definitely not in the conflict clause.
  if(it == tab.end())
    return false;

  // Ask the manager how to update the table.
  // May cause side-effects if the manager is
  // abusing the meaning of data[idx].
  int idx = (*it).second;
  LemmaManager* man(e->managers[l.kind]);
  ResolvableT r(man->is_resolvable(l.data.id, l.data.info, data[idx]));
  if(r == R_NotResolvable)
    return false;

  // Entry is to be erased from the table.
  if(r == R_ResolveElim)
    tab.erase(it);

  // Either way, the lemma has been resolved, and
  // is at the current level.
  count--;

  // If this is the last thing at the
  // current decision level, top here
  // instead of 
  if(count == 0)
  {
    learnt_out.clear();
    learnt_out.push(l);
    
    lem_table::iterator it(tab.begin());

    // Now ask the relevant managers
    // for the remainder of the learnt clause.
    for(; it != tab.end(); ++it)
    {
      lem_sig sig((*it).first);
      int idx = (*it).second;
      LemmaManager* lman(e->managers[sig.kind]);
      lman->collect(sig.id, data[idx], learnt_out);
    }
     
    return true;
  }

  // Shouldn't be resolving a decision literal.
  expln ex(inf.ex);
  assert(ex.kind != Ex_Dec);
  if(ex.kind == Ex_Cl)
  {
    // An existing clause. l should be the 0th element.
    clause* cl(ex.cl);
    
    // Add all the other elements.
    for(int li = 1; li < cl->sz; cl++)
      add_lemma(cl->ls[li]);
  } else {
    // It's a thunk.
    ex_thunk et(ex.ex); 

    // Get the explanation.
    vec<lemma> expln;
    et.fun(et.data, et.cookie, expln);
    
    // Add each element in the explanation
    for(int li = 0; li < expln.size(); li++)
      add_lemma(expln[li]);
  }
  return false;
}
