#ifndef __PHAGE_MANAGER_H__
#define __PHAGE_MANAGER_H__

class AtomManager;

#include "engine/atom.h"
#include "engine/env.h"
#include "engine/sat.h"

// Registering callbacks for when a atom
// becomes true.
typedef int watch_tag;
typedef bool(*watch_callback)(void* data, watch_tag tag, atom_data l_data);
typedef struct {
  watch_callback fun; // The function to call
  void* data;         // Typically the propagator
  watch_tag tag;      // Typically the variable index
} watch_thunk;

class AtomManager {
public:
  AtomManager(env* _e);
  
  // Get a concrete lit for the corresponding
  // atom. May already exist.
  virtual lit bind(_atom& x) = 0;
  // Mark a atom as no longer persistent
  virtual void unbind(_atom& x) { }

  // Attach an event 
  // virtual void watch(atom_id id, watch_thunk& c) = 0;

  // Assert a atom
  virtual bool post(_atom& x, vec<atom>& out_confl) = 0;
  // Can we do this more cheaply?
  // virtual lit undo(_atom& x) = 0;

  // Evaluate a atom under the current state.
  virtual lbool value(_atom& x) = 0;

  // x -> y?
  virtual bool le(_atom& x, _atom& y) = 0;

  // Are all variables managed by this fixed?
  virtual bool is_fixed(void) = 0;

  // Choose a branch literal. Extend to handle
  // branches later.
  virtual atom branch(void) = 0;


  // Conflict clause resolution
  virtual ResolvableT is_resolvable(atom_id id, atom_val val, atom_val prev) = 0;
  virtual void collect(atom_id id, atom_val v, vec<atom>& learnt_out) = 0;

  protected:
    env* e;
    atom_kind kind;
};

#endif
