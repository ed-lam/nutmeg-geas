#include "engine/env.h"

lit env::lit_of_atom(atom& l)
{
  /*
  bool sign = atom_sign(l);
  atom pos = sign ? l : ~l;
  
  atom_map_t::iterator it(atom_map.find(pos));
  if(it != atom_map.end())
  {

  } else {

  }
  */
  assert(0 && "lit_of_atom not yet impatomented.");
  return mk_lit(0, 1);
}

// To evaluate a atom, we just dispatch
// to the relevant manager.
lbool env::atom_val(atom& l)
{
  return managers[l.kind]->value(l.data); 
}
