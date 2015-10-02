#ifndef __PHAGE_ENV_H__
#define __PHAGE_ENV_H__
// Solver environment.
// Mostly stores mapping of atom-kinds to
// managers, and the trail.
#define VERBOSE

class env;

#include "mtl/Vec.h"
#include "mtl/Queue.h"
#include "utils/cache.h"
#include "utils/Magic.h"

#include "engine/atom.h"
#include "engine/manager.h"
#include "engine/propagator.h"
#include "engine/trail.h"
#include "engine/branch.h"

#include "engine/expln.h"
#include "engine/sat.h"

typedef Propagator<env> prop_t;

class atom_inf {
public:
  atom_inf(atom _l, expln _ex)
    : l(_l), ex(_ex)
  { }

  atom l; 
  // Explanation thunk
  expln ex;
};

/*
inline atom_inf mk_inf(atom l, expln ex) {
  atom_inf inf; inf.l = l; inf.ex = ex; return inf;
}
*/

typedef struct {
  AtomManager* man;
  int ref;
} atomid_info;

typedef AutoC<atom, int>::cache atom_map_t;

class env {
public:
  env(void)
    : sat(this)
  { }

  // Allocate a new atom identifier, and
  // initialize the data-structures.
  atom_id new_atom_id(AtomManager* man, int ref);

  void push_level(void) {
    gen_trail.push_level();
    atom_tlim.push(atom_trail.size());
  }

  void pop_level(void) {
    gen_trail.restore_level();

    int lim = atom_tlim.last();
    while(atom_trail.size() > lim)
      atom_trail.pop();
    atom_tlim.pop();
  }

  void attach(atom& a, Watcher* w, int tok);

  void enqueue(prop_t* prop)
  {
    prop_queue.insert(prop);  
  }

  void cleanup_props(void)
  {
    for(int ii = 0; ii < prop_queue.size(); ii++)
      prop_queue[ii]->cleanup(); 
    prop_queue.clear();
  }

  // Add an original clause
  template<typename ... Args>
  bool addClause(const Args&... args)
  {
    vec<atom> ps;
    get_args(ps, args...);

    // Simplify the clause and remove duplicates
    // FIXME: Finish implementing
//    std::sort(ps.begin(), ps.end());
    int ii = 0; 
    while(ii < ps.size() && atom_val(ps[ii]) == l_False)
      ii++;

    if(atom_val(ps[ii]) == l_True)
      return true;

    // Empty clause
    if(ii == ps.size())
      return false;

    ps[0] = ps[ii];
    int jj = 1;
    for(ii++; ii < ps.size(); ii++)
    {
      atom at = ps[ii];
      lbool val = atom_val(at);
      if(val == l_True)
        return true;
      if(val == l_Undef && (at != ps[jj-1]))
        ps[jj++] = at;
    }

    if(jj == 1)
    {
      assert(level() == 0);
      // Post the atom
      post(ps[0], expln());
    }
    ps.shrink(ps.size() - jj);

    return sat.addClause(ps, false);
  }

  template<typename ... Args>
  bool addLearnt(const Args&... args)
  {
    vec<atom> ps;
    get_args(ps, args...);
    
    if(ps.size() == 0)
      return false;
    if(ps.size() == 1)
    {
      assert(level() == 0);
      post(ps[0], expln());
    }
    return sat.addClause(ps, true);
  }

  void post(atom at, const expln& ex, void* origin = NULL);

  AtomManager* atom_man(atom& l);
  _atom to_atom_(atom& l);

  lbool atom_val(atom& l);
  lbool value(atom& l) { return atom_val(l); }

  int false_level(atom& l);

  int level(void) { return atom_tlim.size(); }

  // Mapping of managers for atoms
  // vec<AtomManager*> managers;
  vec<Brancher*> branchers;

  // List of propagators
  vec<prop_t*> propagators;
  Queue<prop_t*> prop_queue;

  Sat<env> sat;

  // Information about allocated atom-ids.
  vec<atomid_info> atid_info;
//  vec<bool> seen;
//  vec<int> conflict_cookie;
//  int num_seen;

  // Trail of inferences that were made.
  vec<int> atom_tlim;
  vec<atom_inf> atom_trail;

  // Data trail
  Trail gen_trail;
};

#endif
