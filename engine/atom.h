#ifndef __PHAGE_LEMMA__
#define __PHAGE_LEMMA__
#include <map>
// Header file for atomic constraints.

// atom_kind indicates the appropriate handler
// for the atom.
// All atoms must be complementable.
typedef int atom_id;
typedef int atom_tok;
typedef int atom_val;

// Will need, eventually, to extend
// id and info to possible pointers.
typedef struct {
  atom_tok tok;      // Identify the sort of atom
  atom_val info;  // The atom's `value'
} atom_data;

typedef atom_data _atom;

typedef struct {
  atom_id id;
  atom_val info;
} atom;


inline _atom mk_atom_(atom_tok tok, atom_val info) {
  _atom l; l.tok = tok; l.info = info;
  return l;
}
inline atom mk_atom(atom_id id, atom_val info) {
  atom l; l.id = id; l.info = info;
  return l;
}

inline bool operator==(const atom& x, const atom& y)
{
  return x.id == y.id && x.info == y.info;
}

inline bool operator!=(const atom& x, const atom& y)
{
  return x.id != y.id || x.info != y.info;
}

inline atom operator~(const atom& l)
{
  return mk_atom(l.id^1, l.info);
}

inline bool atom_sign(const atom& l)
{
//  return (l.id&1) == 0;
  return (l.id&1);
}

inline atom atom_undef(void) {
  atom l;
  l.id = -1;
  l.info = 0;
  return l;
}

/*
typedef struct {

} Atom_hash;
*/

inline atom operator^(atom a, int x) {
  return mk_atom(a.id^x, a.info);
}

typedef struct {
  bool operator()(const atom& x, const atom& y) const
  {
    if(x.id != y.id)
      return x.id < y.id;
    return x.info < y.info; 
  }
} Atom_lt;

typedef struct {
  bool operator()(const atom& x, const atom& y) const
  {
    return x.id == y.id && x.info == y.info;
  }
} Atom_eq;

template <class V>
class AtomMap {
public:
  typedef std::map<atom, V, Atom_lt> t;
};

inline bool atom_is_undef(const atom& l) { return l.id == -1; }

// Flag types
enum ResolvableT { R_NotResolvable, R_ResolveKeep, R_ResolveElim };

#endif