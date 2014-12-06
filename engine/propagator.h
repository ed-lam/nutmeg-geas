#ifndef __PHAGE_PROPAGATOR_H__
#define __PHAGE_PROPAGATOR_H__

class Propagator;

#include "engine/atom.h"
#include "engine/env.h"

class Propagator {
public:
  Propagator(env* _e)
    : e(_e), in_queue(false)
  { }

  virtual bool propagate(vec<atom>& confl) = 0;

  void cleanup(void) {
    in_queue = false;
    _cleanup();
  }
protected:
  virtual void _cleanup(void) { }

  env* e;
  bool in_queue;    
};

#endif
