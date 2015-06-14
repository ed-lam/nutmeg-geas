#ifndef __PHAGE_SAT_H__
#define __PHAGE_SAT_H__
#include "mtl/Vec.h"
#include "engine/base-types.h"
#include "engine/atom.h"
#include "engine/expln.h"
#include "engine/propagator.h"

typedef struct {
  int x;
} lit;

inline lit mk_lit(int x, int sign) {
  lit l = { x<<1|sign }; return l;
}
inline int lvar(lit& l) { return l.x>>1; }
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
class Sat : public Propagator<Host>, public Watcher {
public:
  typedef Sat<Host> Sat_t;

  static void explain(void* p_ptr, expl_cookie cookie, vec<atom>& out_expl)
  {
    Sat_t* ptr = ((Sat_t*) p_ptr);
    lit l = lit_of_int(cookie);
    ptr->explain_inf(l, out_expl);
  }

  Sat(Host* _h)
    : Propagator<Host>(_h), h(_h)
  {
         
  }

  expln make_reason(lit l) {
    return expln(explain, this, (expl_cookie) int_of_lit(l));
  }

  void wakeup(int _l)
  {
    // FIXME: Check l wasn't propagated _from_ here.
    lit l(lit_of_int(_l));
    assert(value(l) == l_True); 
    reason[lvar(l)] = NULL;
    queue.push(l);
    
    ((Propagator<Host>*) this)->enqueue();
  }

  void _cleanup(void)
  {
    queue.clear();
  }

  bool propagate(vec<atom>& confl)
  {
    printf("Propagating SAT.\n");

    int qhead = 0; 
    
    for(; qhead < queue.size(); qhead++)
    {
      printf("queue: [");
      for(lit l : queue)
        printf(" %s%d", lsgn(l) ? "" : "-", lvar(l));
      printf("]\n");

      lit l(queue[qhead]);
      assert(int_of_lit(l) < watches.size());

      vec<Clause*>& ws(watches[int_of_lit(l)]);
      printf(" processing lit(%s%d); %d watches.\n", lsgn(l) ? "" : "-", lvar(l), ws.size());

      int ii = 0;
      int jj = 0;
      for(; jj < ws.size(); jj++)
      {
        Clause& w(*(ws[jj]));
        printf("  checking watch for clause %p. (%d watches)\n", (void *) (&w), ws.size());
        // Ensure ~l is second watch.
        if(w[1] != ~l)
        {
          assert(w[0] == ~l);
          w[0] = w[1];
          w[1] = ~l;
        }

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
        assert(kp <= end);
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
          ws.shrink(jj-ii);
          
          return false;
        } else {
          // Unit propagation
          // Save watch
          ws[ii++] = &w; 
          queue.push(l0);
          reason[lvar(l0)] = &w;
          
          h->post(lit_atom(l0), make_reason(l0), this);
          continue;
        }
watch_found:
        lit l_watch(*kp);
        assert((~l_watch) != l);
        w[1] = l_watch;
        *kp = ~l;
        watches[int_of_lit(~l_watch)].push(&w);
      }
      ws.shrink(jj-ii);
    }
    
    return true;
  }

  void explain_inf(lit l, vec<atom>& out_expl)
  {
    assert(0 && "SAT::explain_inf not yet implemented."); 
  }

  // Doesn't do any simplification of the clauses,
  // and assumes the watches are correct.
  bool addClause(vec<atom>& ps, bool is_learnt = false)
  {
    vec<lit> lits;
    for(atom a : ps)
    {
      lits.push(atom_lit(a));
    }
    
    Clause* cl = Clause_new(lits); 
    attachClause(cl);
    return true;
  }

  void attachClause(Clause* cl)
  {
    int l0 = int_of_lit(~(*cl)[0]);
    int l1 = int_of_lit(~(*cl)[1]);
    watches[l0].push(cl);
    watches[l1].push(cl);

    for(lit l : *cl)
    {
      int li = int_of_lit(~l);
      if(!is_attached[li])
      {
        h->attach(atoms[li], this, li);
        is_attached[li] = true;
      }
    }
  }

  /*
  template<typename T>
  bool addClause(vec<atom>& ps, const T& p, bool is_learnt)
  {
    ps.push((atom) p);
    return addClause(ps, is_learnt);
  }

  template<typename T>
  bool addClause(vec<atom>& ps, const T& p)
  {
    ps.push((atom) p);
    return addClause(ps);
  }

  template<typename T, typename ... Args>
  bool addClause(vec<atom>& ps, const T& p, const Args&... args)
  {
    ps.push((atom) p);
    return addClause<Args ...>(ps, args...);
  }

  template<typename ... Args>
  bool addClause_(const Args&... args)
  {
    vec<atom> ps;
    return addClause<Args...>(ps, args...);
  }
  */

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
    if(it != atom_names.end())
    {
      return (*it).second^a_sign;
    } else {
      // Allocate a new variable 
      lit l = lit_of_int(atoms.size());
      atoms.push(a_low);
      atoms.push(~a_low);
      is_attached.push(false);
      is_attached.push(false);
      watches.push();
      watches.push();
      reason.push(NULL);
      atom_names.insert(std::make_pair(a_low, l));
      return l^a_sign;
    }
  }

  Host* h;

  vec<lit> queue;
  vec<atom> atoms;
  vec<bool> is_attached;
  AtomMap<lit>::t atom_names;
  vec< vec<Clause*> > watches;
  vec<Clause*> reason;
};
#endif
