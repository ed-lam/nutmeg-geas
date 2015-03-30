#include "engine/env.h"
  
atom_id env::new_atom_id(AtomManager* man, int ref)
{
  atom_id id(atid_info.size()); 
  atomid_info info = { man, ref };
  
  atid_info.push(info);
  seen.push(false);
  seen.push(false);
  conflict_cookie.push(0);
  conflict_cookie.push(0);

  return id;
}

AtomManager* env::atom_man(atom& l)
{
  return atid_info[l.id].man;
}

void env::attach(atom& a, Watcher* w, int tok)
  {
    atom_man(a)->attach(to_atom_(a), w, tok);
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
