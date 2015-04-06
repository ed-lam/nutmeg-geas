#ifndef __PHAGE_PROPAGATOR_H__
#define __PHAGE_PROPAGATOR_H__

// class Propagator;

#include "engine/atom.h"

template<class Host>
class Propagator {
public:
  Propagator(Host* _h)
    : h(_h), in_queue(false)
  { }

  virtual bool propagate(vec<atom>& confl) = 0;

  void cleanup(void) {
    in_queue = false;
    _cleanup();
  }

  void enqueue(void) {
    if(!in_queue)
    {
      in_queue = true;
      h->enqueue(this);
    }
  }

protected:
  virtual void _cleanup(void) { }

  Host* h;
  bool in_queue;    
};

#endif
