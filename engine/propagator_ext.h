#ifndef PHAGE__PROPAGATOR_EXT_H
#define PHAGE__PROPAGATOR_EXT_H
// Header file for syntactic-sugar templated
// function definitions
#include "solver/solver_data.h"
namespace phage {

template<class T>
inline void propagator::set(trailed<T>& x, T k) {
  x.set(s->persist, k);
}

}
#endif
