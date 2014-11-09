#include "engine/env.h"

lit env::lit_of_lemma(lemma& l)
{
  /*
  bool sign = lem_sign(l);
  lemma pos = sign ? l : ~l;
  
  lem_map_t::iterator it(lem_map.find(pos));
  if(it != lem_map.end())
  {

  } else {

  }
  */
  assert(0 && "lit_of_lemma not yet implemented.");
  return mk_lit(0, 1);
}

// To evaluate a lemma, we just dispatch
// to the relevant manager.
lbool env::lem_val(lemma& l)
{
  return managers[l.kind]->value(l.data); 
}
