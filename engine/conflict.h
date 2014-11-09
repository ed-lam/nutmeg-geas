#ifndef __PHAGE_CONFLICT_H__
#define __PHAGE_CONFLICT_H__
#include "utils/cache.h"
#include "engine/lemma.h"

// Class declarations for handling
// conflict analysis.

// conflict_state manages the store of 'seen' lemmas.
class conflict_state {
  class lem_sig {
  public:
    lem_sig(lem_kind _kind, lem_id _id)
      : kind(_kind), id(_id)
    { }
    lem_kind kind;
    lem_id id;
  };
  typedef typename AutoC<lem_sig, int>::cache lem_table;

public:
  conflict_state(env* _e)
    : e(_e)
  { }

  // Update the conflict clause with a trail element.
  bool update(lem_inf& inf, vec<lemma>& out_learnt);
  void add_lemma(lemma l);

  int seen_count(void) { return count; }
protected:
  env* e;

  lem_table tab;
  vec<lem_val> data;
  int count;
};

#endif
