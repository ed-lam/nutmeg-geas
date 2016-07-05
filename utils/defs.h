#ifndef PHAGE_DEFS__H
#define PHAGE_DEFS__H
// Syntactic sugar definitions
#include <cassert>
#include <cstdio>

#include "mtl/Vec.h"

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

template<class T>
struct range_t {
  range_t(T* pre, T* post) 
    : _pre(pre), _post(post) { }
  
  T* begin(void) const { return _pre; }
  T* end(void) const { return _post; }

  T* _pre;
  T* _post;
};

template<class T>
struct rev_range_t {
  rev_range_t(T* pre, T* post) 
    : _pre(pre), _post(post) { }
  
  struct iterator {
    iterator(T* _p) : p(_p) { }
    bool operator!=(const iterator& o) const { return p != o.p; }
    iterator& operator++(void) { --p; return *this; }
    T& operator*(void) { return *p; }
    T* p;
  };

  iterator begin(void) const { return iterator(_post-1); }
  iterator end(void) const { return iterator(_pre-1); }

  T* _pre;
  T* _post;
};

template<class T>
range_t<T> range(T* start, T* end) {
  return range_t<T>(start, end);
}
template<class T>
rev_range_t<T> rev_range(T* start, T* end) {
  return rev_range_t<T>(start, end);
}
#endif
