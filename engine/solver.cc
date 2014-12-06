// Top-level solver procedure.
#include "engine/solver.h"
#include "engine/conflict.h"

static expln expl_none = {
  Ex_Dec  
};

solver::RESULT solver::solve(void)
{
  vec<atom> confl;

  while(1)
  {
    if(!propagate(confl))
    {
      // Conflict
      if(decisionLevel() == root)
        return UNSAT;

      vec<atom> out_learnt;
      // Compute a conflict clause.
      analyzeConflict(confl, out_learnt);
      // Unroll the solver to the appropriate level
      backtrack_with(out_learnt);
      // Instantiate the atom literals and add
      // it to the clause database.
      post_learnt(out_learnt);
    } else {
      atom d = pick_branch(); 
      if(atom_is_undef(d))
        return SAT;
      
      post_branch(d);
    }
  }
  // Should never be reached.
  assert(0 && "Unreachable.");
  return UNSAT;
}

bool solver::propagate(vec<atom>& confl)
{
  // Walk the trail, dispatching to each of the managers
  // FIXME: Handle propagator cleanup on failure.
  do
  {
    while(atom_head < e->atom_trail.size())
    {
      atom l(e->atom_trail[atom_head++].l); 

      if(!(e->managers[l.kind]->post(l.data, confl)))
        return false;
      
      e->gen_trail.commit();
    }

    if(!prop_queue.empty())
    {
      Propagator* p(e->propagators[prop_queue._pop()]);

      if(!p->propagate(confl))
        return false;

      e->gen_trail.commit();
    }
  } while(atom_head < e->atom_trail.size() || !prop_queue.empty());
  
  return true;
}

atom solver::pick_branch(void)
{
  // Do something clever here.
  for(int mi = 0; mi < e->managers.size(); mi++)
  {
    atom l(e->managers[mi]->branch());
    if(!atom_is_undef(l))
      return l;
  }
  return atom_undef();
}

void solver::post_branch(atom l)
{
  e->push_level();
  post_atom(l, expl_none); 
}

void solver::analyzeConflict(vec<atom>& confl, vec<atom>& out_learnt)
{
  conflict_state cstate(e);
  for(int li = 0; li < confl.size(); li++)
    cstate.add_atom(confl[li]);

  atom_inf inf(e->atom_trail.last());
  while(!cstate.update(inf, out_learnt))
  {
    // Handle backtracking somewhere.
    e->atom_trail.pop();
    inf = e->atom_trail.last();
  }
  // conflict_state::update should have left the 1-UIP clause in out_learnt.
  return;
}

// Find the backtrack level for a given 
void solver::backtrack_with(vec<atom>& out_learnt)
{
  assert (0 && "backtrack_with not impatomented.");
}

void solver::post_learnt(vec<atom>& out_learnt)
{
  assert (0 && "post_learnt not impatomented.");
}
