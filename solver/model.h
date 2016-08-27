#ifndef PHAGE_MODEL_H
#define PHAGE_MODEL_H
#include "mtl/Vec.h"
#include "engine/phage-types.h"

namespace phage {

struct model {
  model(void) { };

  pval_t get(pid_t pi) const {
    if(pi&1) {
      return pval_max - vals[pi>>1];
    } else {
      return vals[pi>>1];
    }
  }

  template<class T>
  typename T::val_t operator[](const T& v) {
    return v.model_val(*this);
  }

  vec<pval_t> vals;
};

}

#endif
