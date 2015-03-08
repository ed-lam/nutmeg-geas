#ifndef __VAR_INTERFACE_H__
#define __VAR_INTERFACE_H__
#include "engine/atom.h"

template<class T, class C>
class NumVar {
public:
  atom operator<=(const T& k) { return impl()->atom_le(k); }
  atom operator<(const T& k) { return impl()->atom_lt(k); }
  atom operator==(const T& k) { return impl()->atom_eq(k); }
  atom operator>(const T& k) { return ~ impl()->atom_le(k); }
  atom operator>=(const T& k) { return ~ impl()->atom_lt(k); }

  friend T lb(C& x) { return x.lb(); }
  friend T ub(C& x) { return x.ub(); }
  friend bool in_domain(C& x) { return x.in_domain(); }

  inline C* impl(void) { return static_cast<T*>(this); }
};

// a * x + c
/*
template<class T>
class IntView : public NumVar<int, IntView> {
public:
  IntView(int _a, NumVar<int, T>* x, int _c)
    : x(_x), a(_a), k(_c)
  { assert(a > 0); }

  // FIXME: Correct rounding for a != 1
  atom atom_le(int k) { return (*x) <= (k-c)/a; }
  atom atom_lt(int k) { return (*x) < (k-c)/a; }
  atom atom_eq(int k) {
    int v = (k-c);
    if(v % a == 0)
      return (*x) == (v/a);
    else
      // FIXME: SHOULD BE FALSE
      return (*x) == (v/a);
  }
  
  int lb(void) { return a*(x->lb()) + c; };
  int ub(void) { return a*(x->ub()) + c; };
  friend T lb(C& x) { return x.lb(); }
  friend T ub(C& x) { return x.ub(); }
  friend bool in_domain(C& x) { return x.in_domain(); }

  inline C* impl(void) { return static_cast<T*>(this); }
protected:
  NumVar<int, T>* x;
  int a;
  int c;
};
*/

#endif
