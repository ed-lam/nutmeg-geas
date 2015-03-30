#ifndef PHAGE_EXPLN_H__
#define PHAGE_EXPLN_H__

enum expl_kind { Ex_Dec, Ex_Cl, Ex_Fun };
enum expl_tag { Ex_Keep = 1 };
typedef int expl_cookie;

// Definition of deferred explanations.
typedef void(*expl_fun)(void* data, expl_cookie cookie, vec<atom>& out_expl);
typedef int expl_cookie;
typedef struct {
  expl_fun fun;       // The function to call
  void* data;         // Typically the propagator
  expl_cookie cookie; // Typically the variable index
} ex_thunk;

/*
typedef struct {
  expl_kind kind;
  union {
    ex_thunk ex;
    void* cl;
  };
} expln;
*/

class expln {
public:
  expln()
    : kind(Ex_Dec)
  { }

  expln(expl_fun _fun, void* _data, expl_cookie _cookie)
    : kind(Ex_Fun)
  {
    ex.fun = _fun;
    ex.data = _data;
    ex.cookie = _cookie;  
  }
  
  void operator()(vec<atom>& out_expl) {
    assert(kind == Ex_Fun);  
    ex.fun(ex.data, ex.cookie, out_expl);
  }

  expl_kind kind;
  void* data;
  union {
    ex_thunk ex;
    void* cl;
  };
};

/*
inline expln mk_expl_thunk(expl_fun fun, void* data, expl_cookie cookie)
{
  expln e;
  e.kind = Ex_Fun;
  e.ex.fun = fun;
  e.ex.data = data;
  e.ex.cookie = cookie;
  return e;
}
*/
 
#endif
