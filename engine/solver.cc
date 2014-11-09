// Top-level solver procedure.
#include "engine/solver.h"
#include "engine/conflict.h"

static expln expl_none = {
  Ex_Dec  
};

solver::RESULT solver::solve(void)
{
  vec<lemma> confl;

  while(1)
  {
    if(!propagate(confl))
    {
      // Conflict
      if(decisionLevel() == root)
        return UNSAT;

      vec<lemma> out_learnt;
      // Compute a conflict clause.
      analyzeConflict(confl, out_learnt);
      // Unroll the solver to the appropriate level
      backtrack_with(out_learnt);
      // Instantiate the lemma literals and add
      // it to the clause database.
      post_learnt(out_learnt);
    } else {
      lemma d = pick_branch(); 
      if(lem_is_undef(d))
        return SAT;
      
      post_branch(d);
    }
  }
  // Should never be reached.
  return UNSAT;
}

bool solver::propagate(vec<lemma>& confl)
{
  // Walk the trail, dispatching to each of the managers
  // FIXME: Handle propagator cleanup on failure.
  do
  {
    while(lem_head < e->lem_trail.size())
    {
      lemma l(e->lem_trail[lem_head++].l); 

      if(!(e->managers[l.kind]->post(l.data, confl)))
        return false;
    }

    if(!prop_queue.empty())
    {
      Propagator* p(e->propagators[prop_queue._pop()]);

      if(!p->propagate(confl))
        return false;
    }
  } while(lem_head < e->lem_trail.size() || !prop_queue.empty());
  
  return true;
}

lemma solver::pick_branch(void)
{
  return lem_undef();
}

void solver::post_branch(lemma l)
{
  e->push_level();
  post_lemma(l, expl_none); 
}

void solver::analyzeConflict(vec<lemma>& confl, vec<lemma>& out_learnt)
{
  conflict_state cstate(e);
  for(int li = 0; li < confl.size(); li++)
    cstate.add_lemma(confl[li]);

  lem_inf inf(e->lem_trail.last());
  while(!cstate.update(inf, out_learnt))
  {
    // Handle backtracking somewhere.
    e->lem_trail.pop();
    inf = e->lem_trail.last();
  }
  // conflict_state::update should have left the 1-UIP clause in out_learnt.
  return;
}

// Find the backtrack level for a given 
void solver::backtrack_with(vec<lemma>& out_learnt)
{
  assert (0 && "backtrack_with not implemented.");
}

void solver::post_learnt(vec<lemma>& out_learnt)
{
  assert (0 && "post_learnt not implemented.");
}
