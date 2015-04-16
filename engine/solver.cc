// Top-level solver procedure.
#include "engine/solver.h"
#include "engine/conflict.h"

typedef Propagator<env> prop_t;

static expln expl_none;

solver::solver(env* _e)
    : e(_e), root(0), atom_head(0)
{
}

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
//      confl_info.analyze_conflict(e, confl, out_learnt);
      // NAIVE: Just pick the decision nogood.
      for(int ll = 0; ll < e->level(); ll++)
        out_learnt.push(~(e->atom_trail[e->atom_tlim[ll]].l));

      printf("Learnt: [");
      for(atom at : out_learnt)
        printf(" %s(%d, %d)", at.id&1 ? "" : "-", at.id>>1, at.info);
      printf(" ]\n");
      // Unroll the solver to the appropriate level
      backtrack_with(out_learnt);
      atom_head = e->atom_trail.size();
      // Instantiate the atom literals and add
      // it to the clause database.
      post_learnt(out_learnt);
    } else {
      atom d = pick_branch(); 
      if(atom_is_undef(d))
        return SAT;
      
      printf("Branch: %s(%d, %d)\n", d.id&1 ? "" : "-", d.id, d.id>>1);
      post_branch(d);
    }
  }
  // Should never be reached.
  assert(0 && "Unreachable.");
  return UNSAT;
}

void solver::cleanup_props(void)
{
  while(!e->prop_queue.empty())
  {
    e->prop_queue._pop()->cleanup();
  }
}

bool solver::propagate(vec<atom>& confl)
{
  // Walk the trail, dispatching to each of the managers
  do
  {
    while(atom_head < e->atom_trail.size())
    {
      e->gen_trail.tick();
      atom_inf& inf(e->atom_trail[atom_head++]);
      atom l(inf.l);
      AtomManager* lman(e->atom_man(l));
      if(!(lman->post(e->to_atom_(l))))
      {
//        inf.ex(confl);
        return false;
      }
    }

    if(!e->prop_queue.empty())
    {
      prop_t* p(e->prop_queue._pop());

      if(!p->propagate(confl))
      {
        p->cleanup();
        cleanup_props();
        return false;
      }
      p->cleanup();

      e->gen_trail.tick();
    }
  } while(atom_head < e->atom_trail.size() || !e->prop_queue.empty());
  
  return true;
}

atom solver::pick_branch(void)
{
  // Do something clever here.
  for(Brancher* b : e->branchers)
  {
    atom l(b->branch());
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

// Find the backtrack level for a given learnt clause.
// Also ensures the watches are in the correct locations.
int solver::find_btlevel(vec<atom>& out_learnt)
{
  if(out_learnt.size() < 2)
    return root;
  
  assert(e->false_level(out_learnt[0]) == e->level());

  int lev_id = 1;
  int lev = e->false_level(out_learnt[1]);

  for(int li = 2; li < out_learnt.size(); li++)
  {
    int llev = e->false_level(out_learnt[li]); 
    if(llev > lev)
    {
      lev_id = li;
      lev = llev;
    }
  }
  assert(lev < e->level());
  std::swap(out_learnt[1], out_learnt[lev_id]);
  return lev;
}

void solver::backtrack_with(vec<atom>& out_learnt)
{
//  assert (0 && "backtrack_with not impatomented.");
  assert(e->false_level(out_learnt[0]) == e->level());
  int btlevel = find_btlevel(out_learnt);

  printf("Backtracking from %d to %d.\n", e->level(), btlevel);
  for(int l = e->level(); btlevel < l; l--)
    e->pop_level();
  assert(e->level() == btlevel);
}

void solver::post_learnt(vec<atom>& out_learnt)
{
  assert(out_learnt.size() > 0);
  assert(e->value(out_learnt[0]) == l_Undef);

  if(out_learnt.size() == 1)
    post_atom(out_learnt[0], expl_none); // Fix explanation
  else
    e->sat.addClause(out_learnt, true);
}
