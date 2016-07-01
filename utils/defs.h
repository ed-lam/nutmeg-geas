#ifndef PHAGE_DEFS__H
#define PHAGE_DEFS__H
// Syntactic sugar definitions
#include <cassert>
#include <cstdio>

#define NOT_YET assert(0 && "Not yet implemented.")
#define NOT_YET_WARN fprintf(stderr, "WARNING: Incompletely implemented.\n")
#define ERROR assert(0 && "FAILURE.")

template<class T, class U>
void vec_push(vec<T>& vec, U& elt) { vec.push(elt); }

template<class T, class U, class... Us>
void vec_push(vec<T>& vec, U& elt, Us... rest) {
  vec.push(elt);
  vec_push(vec, rest...);
}
#endif
