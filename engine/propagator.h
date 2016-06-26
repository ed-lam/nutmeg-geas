#ifndef PHAGE_PROPAGATOR__H
#define PHAGE_PROPAGATOR__H
#include "engine/infer-types.h"

namespace phage {

class propagator {
public: 
  virtual bool propagate(vec<clause_elt>& confl) = 0;
};

}
#endif
