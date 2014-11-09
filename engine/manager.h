#ifndef __PHAGE_MANAGER_H__
#define __PHAGE_MANAGER_H__

class LemmaManager;

#include "engine/lemma.h"
#include "engine/env.h"
#include "engine/sat.h"

// Registering callbacks for when a lemma
// becomes true.
typedef int watch_tag;
typedef bool(*watch_callback)(void* data, watch_tag tag, lem_data l_data);
typedef struct {
  watch_callback fun; // The function to call
  void* data;         // Typically the propagator
  watch_tag tag;      // Typically the variable index
} watch_thunk;

class LemmaManager {
public:
  LemmaManager(env* _e);
  
  // Get a concrete lit for the corresponding
  // lemma. May already exist.
  virtual lit bind(_lemma& x) = 0;
  // Mark a lemma as no longer persistent
  virtual void unbind(_lemma& x) { }

  // Attach an event 
  // virtual void watch(lem_id id, watch_thunk& c) = 0;

  // Assert a lemma
  virtual bool post(_lemma& x, vec<lemma>& out_confl) = 0;
  // Can we do this more cheaply?
  // virtual lit undo(_lemma& x) = 0;

  // x -> y?
  virtual bool le(_lemma& x, _lemma& y) = 0;

  // Are all variables managed by this fixed?
  virtual bool is_fixed(void) = 0;

  // Choose a branch literal. Extend to handle
  // branches later.
  virtual _lemma branch(void) = 0;


  // Conflict clause resolution
  virtual ResolvableT is_resolvable(lem_id id, lem_val val, lem_val prev) = 0;
  virtual void collect(lem_id id, lem_val v, vec<lemma>& learnt_out) = 0;

  protected:
    env* e;
    lem_kind kind;
};

#endif
