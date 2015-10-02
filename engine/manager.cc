#include "engine/atom.h"
#include "engine/manager.h"

AtomManager::AtomManager(env* _e)
  : e(_e)
{ }

atom AtomManager::from_atom_(_atom x)
{
  atom_id id = tok_ids[x.token()];
  return atom(id, x.info, x.sign());
}

atom_tok AtomManager::new_atom_tok(void)
{
  atom_tok tok(tok_ids.size());
  atom_id id(e->new_atom_id(this, tok));
  tok_ids.push(id);

  return tok;
}
