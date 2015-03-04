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

AtomManager* env::atom_man(atom& l)
{
  return atid_info[l.id].man;
}

_atom env::to_atom_(atom& l)
{
  return mk_atom_(atid_info[l.id].ref, l.info);
}

lbool env::atom_val(atom& l)
{
  _atom _l(to_atom_(l));
  return atom_man(l)->value(_l);
}
