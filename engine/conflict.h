#ifndef __PHAGE_CONFLICT_H__
#define __PHAGE_CONFLICT_H__
#include "utils/cache.h"
#include "engine/atom.h"

// Class declarations for handling
// conflict analysis.

// conflict_state manages the store of 'seen' atoms.
class conflict_state {
  class atom_sig {
  public:
    atom_sig(atom_kind _kind, atom_id _id)
      : kind(_kind), id(_id)
    { }
    atom_kind kind;
    atom_id id;
  };
  typedef typename AutoC<atom_sig, int>::cache atom_table;

public:
  conflict_state(env* _e)
    : e(_e)
  { }

  // Update the conflict clause with a trail eatoment.
  bool update(atom_inf& inf, vec<atom>& out_learnt);
  void add_atom(atom l);

  int seen_count(void) { return count; }
protected:
  env* e;

  atom_table tab;
  vec<atom_val> data;
  int count;
};

#endif
