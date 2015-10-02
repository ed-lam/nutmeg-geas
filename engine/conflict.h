#ifndef __PHAGE_CONFLICT_H__
#define __PHAGE_CONFLICT_H__
#include "utils/cache.h"
#include "engine/atom.h"
#include "engine/env.h"

// Class declarations for handling
// conflict analysis.

// conflict_state manages the store of 'seen' atoms.
class conflict_state {
public:
  conflict_state(void)
    : count(0)
  { }

  void grow_to(int sz)
  {
    while(seen.size() < sz)
    {
      seen.push(false);
      data.push(0);
      cookie.push(0);
    }
  }

  void add_atom(env* e, atom inf);
  bool update_resolvent(env* e, atom_inf& inf, vec<atom>& learnt_out);
  void analyze_conflict(env* e, vec<atom>& confl, vec<atom>& out_learnt);

  vec<bool> seen;
  vec<atom_val> data;
  vec<atom_val> cookie; 
  int count;
};

#endif
