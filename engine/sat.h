#ifndef __PHAGE_SAT_H__
#define __PHAGE_SAT_H__
#include "mtl/Vec.h"
#include "engine/base-types.h"
#include "engine/atom.h"
#include "engine/expln.h"

typedef struct {
  int x;
} lit;

inline lit mk_lit(int x, int sign) {
  lit l = { x<<1|sign }; return l;
}
inline int lvar(lit& l) { return l.x<<1; }
inline int lsgn(lit& l) { return l.x&1; }
inline lit operator~(lit& l) {
  lit m = { l.x^1 };
  return m;
}
inline int int_of_lit(lit l) { return l.x; }
inline lit lit_of_int(int x) {
  lit l = { x }; return l;
}
inline bool operator==(lit lx, lit ly) {
  return lx.x == ly.x;
}
inline bool operator!=(lit lx, lit ly) {
  return lx.x != ly.x;
}
inline lit operator^(lit x, int v) {
  return lit_of_int(x.x^v);
}

// GKG: Eventually embed the atom in the clause,
// so we don't always have to deref.
/*
typedef struct {
  atom a;
  lit l;
} cl_elt;
*/
typedef lit cl_elt;

class Clause {
public:
  template<class V>
  Clause(V& ps)
    : sz(ps.size())
  {
    int ii = 0;
    for(cl_elt& p : ps)
      data[ii++] = p;
  }

  cl_elt* begin() { return data; }
  cl_elt* tail() { return data+2; }
  cl_elt* end() { return data+sz; }
  cl_elt& operator[](int i) {
    return data[i];
  }
  
protected:
  int sz;
  cl_elt data[0];
};

template<class V>
Clause* Clause_new(V& ps)
{
  void* mem = malloc(sizeof(Clause) + sizeof(cl_elt)*ps.size());
  return new (mem) Clause(ps);
}

template<class Host>
class Sat {
public:
  typedef Sat<Host> Sat_t;

  static void explain(void* p_ptr, expl_cookie cookie, vec<atom>& out_expl)
  {
    Sat_t* ptr = ((Sat_t*) p_ptr);
    lit l = lit_of_int(cookie);
    ptr->explain_inf(l, out_expl);
  }

  Sat(Host* _h)
    : h(_h)
  {
         
  }

  expln make_reason(lit l) {
    return expln(explain, this, (expl_cookie) int_of_lit(l));
  }

  void wakeup(int _l)
  {
    lit l(lit_of_int(_l));
    assert(value(l) == l_True); 
    reason[lvar(l)] = NULL;
    queue.push(l);
  }


  bool propagate(void)
  {
    int qhead = 0; 

    for(; qhead < queue.size(); qhead++)
    {
      lit l(queue[qhead]);
      vec<Clause*>& ws(watches[int_of_lit(l)]);

      int ii = 0;
      int jj = 0;
      for(; jj < ws.size(); jj++)
      {
        Clause& w(*(ws[jj]));
        // Ensure ~l is second watch.
        if(w[1] != ~l)
          w[0] = w[1];

        lit l0(w[0]);
        lbool v0(value(l0));

        if(v0 == l_True)
        {
          // Clause already satisfied.
          w[1] = ~l;
          ws[ii++] = &w;
          continue;
        }
        
        // Look for a replacement watch.
        cl_elt* kp(w.tail()); 
        cl_elt* end(w.end());
        for(; kp != end; kp++)
        {
          if(value(*kp) != l_False)
            goto watch_found;
        }

        // No new watch; ensure w remains correct.
        w[1] = ~l;
        if(v0 == l_False)
        {
          // Conflict.
          while(jj < ws.size())
            ws[ii++] = ws[jj++];
          
          queue.push(l0);
          reason[lvar(l0)] = &w;
              
        } else {
          // Unit propagation
          // Save watch
          ws[ii++] = &w; 
          
          h->post(lit_atom(l), make_reason(&w)); 
        }
watch_found:
        lit l_watch(*kp);
        w[1] = l_watch;
        *kp = ~l;
        watches[int_of_lit(~l_watch)].push(w);
      }
      ws.shrink(jj-ii);
    }
  }

  void explain_inf(lit l, vec<atom>& out_expl)
  {
    assert(0 && "SAT::explain_inf not yet implemented."); 
  }

  // Convert a bunch of 
  template<class V>
  bool addClause(V& ps, bool is_learnt)
  {
    vec<lit> lits;
    for(atom a : ps)
      lits.push(atom_lit(a));
  }

protected:
  lbool value(lit l)
  {
    return h->value(atoms[int_of_lit(l)]);
  }

  atom lit_atom(lit l)
  {
    return atoms[int_of_lit(l)];
  }

  lit atom_lit(atom a)
  {
    // Table stores the negative
    // form of atoms. Because of reasons.
    bool a_sign = atom_sign(a);
    atom a_low = a^a_sign;
    auto it = atom_names.find(a_low);
    if(*it != atom_names.end())
    {
      return (*it).second^a_sign;
    } else {
      // Allocate a new variable 
      lit l = lit_of_int(atoms.size());
      atoms.push(a_low);
      atoms.push(~a_low);
      atom_names.insert(std::make_pair(a_low, l));
      return l^a_sign;
    }
  }

  Host* h;
  
  vec<lit> queue;
  vec<atom> atoms;
  AtomMap<lit>::t atom_names;
  vec< vec<Clause*> > watches;
  vec<Clause*> reason;
};
#endif
