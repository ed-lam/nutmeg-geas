#ifndef __PHAGE_MANAGER_H__
#define __PHAGE_MANAGER_H__

class AtomManager;

#include "engine/base-types.h"
#include "engine/atom.h"
#include "engine/env.h"
#include "engine/sat.h"

// Registering callbacks for when a atom
// becomes true.
/*
typedef int watch_tag;
typedef bool(*watch_callback)(void* data, watch_tag tag, atom_data l_data);
typedef struct {
  watch_callback fun; // The function to call
  void* data;         // Typically the propagator
  watch_tag tag;      // Typically the variable index
} watch_thunk;
*/
class WatchElt {
public:
  WatchElt(Watcher* _w, int _k)
    : w(_w), k(_k)
  { }
  Watcher* w;
  int k;
};

class AtomManager {
public:
  AtomManager(env* _e);

  atom from_atom_(_atom x);
  
  // Must be able to trigger on specific atoms.
  virtual void attach(_atom x, Watcher* w, int id) = 0;
  // Mark a atom as no longer persistent
  virtual void detach(_atom x) { }

  // Attach an event 
  // virtual void watch(atom_id id, watch_thunk& c) = 0;

  // Assert a atom
  virtual bool post(_atom x, void* origin) = 0;
  // Can we do this more cheaply?
  // virtual lit undo(_atom x) = 0;

  // Evaluate a atom under the current state.
  virtual lbool value(_atom x) = 0;

  // What level did x become false?
  virtual int false_level(_atom x) = 0;

  // x -> y?
  virtual bool le(_atom x, _atom y) = 0;

  // Are all variables managed by this fixed?
  virtual bool is_fixed(void) = 0;

  // Choose a branch literal. Extend to handle
  // branches later.
//  virtual atom branch(void) = 0;

  // Conflict clause resolution
  /*
  virtual ResolvableT is_resolvable(atom_id id, atom_val val, atom_val prev) = 0;
  virtual void add_conflict_atom(_atom x) = 0;
  virtual void collect(atom_id id, atom_val v, vec<atom>& learnt_out) = 0;
  */
  virtual ResolvableT is_resolvable(atom_id id, atom_val val, atom_val prev)  {
    assert(0 && "Not implemented.");
    return R_NotResolvable;  
  }
  virtual void add_conflict_atom(_atom x) {
    assert(0 && "Not implemented.");
  }
  virtual void collect(atom_id id, atom_val v, vec<atom>& learnt_out) {
    assert(0 && "Not implemented.");
  }


  protected:
    // Allocate a new atom-token.
    atom_tok new_atom_tok(void);

    vec<atom_id> tok_ids;
    env* e;
};

#endif
