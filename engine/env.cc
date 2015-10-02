#include "engine/env.h"
  
atom_id env::new_atom_id(AtomManager* man, int ref)
{
  atom_id id(atid_info.size()); 
  atomid_info info = { man, ref };
  
  atid_info.push(info);
  // GKG: Now dealt with in conflict_state
//  seen.push(false);
//  seen.push(false);
//  conflict_cookie.push(0);
//  conflict_cookie.push(0);

  return id;
}

AtomManager* env::atom_man(atom& l)
{
  return atid_info[l.id>>1].man;
}

void env::post(atom a, const expln& ex, void* origin)
{
  atom_trail.push(atom_inf(a, ex));
  bool okay = atom_man(a)->post(to_atom_(a), origin);
  assert(okay);
}

void env::attach(atom& a, Watcher* w, int tok)
{
  atom_man(a)->attach(to_atom_(a), w, tok);
}

_atom env::to_atom_(atom& l)
{
  atom_tok tok = atid_info[l.id>>1].ref;
  return _atom(tok, l.info, l.id&1);
}

lbool env::atom_val(atom& l)
{
  _atom _l(to_atom_(l));
  return atom_man(l)->value(_l);
}

int env::false_level(atom& l)
{
  _atom _l(to_atom_(l));
  return atom_man(l)->false_level(_l);
}
