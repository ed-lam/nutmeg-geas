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
class atom_data {
public:
  // FIXME: Be careful with sign extension.
  atom_data(atom_tok _tok, atom_val _val, bool sign)
    : tok(_tok<<1|sign), info(_val)
  { }

protected:
  atom_data(atom_tok _tok, atom_val _info)
    : tok(_tok), info(_info)
  { }

public:
  inline atom_tok token(void) const { return tok>>1; }
  inline int val(void) const { return info; }
  inline bool sign(void) const { return tok&1; }

  atom_data operator~(void) const {
    return atom_data(tok^1, info);
  }

  atom_tok tok;      // Identify the sort of atom
  atom_val info;  // The atom's `value'
};

typedef atom_data _atom;

class atom {
public:
  atom(atom_id _id, atom_val _info, bool sign)
    : id(_id<<1|sign), info(_info)
  { }
protected:
  atom(atom_id _id, atom_val _info)
    : id(_id), info(_info)
  { } 

public:
  static inline atom undef(void) { return atom(-1, 0); }

  inline bool sign(void) const {
    return id&1;
  }

  inline atom operator~(void) const {
    return atom(id^1, info);
  }
  inline atom operator^(int x) const {
    return atom(id^x, info);
  }

  atom_id id;
  atom_val info;
};


/*
inline _atom mk_atom_(atom_tok tok, atom_val info) {
  _atom l; l.tok = tok; l.info = info;
  return l;
}
inline atom mk_atom(atom_id id, atom_val info) {
  atom l; l.id = id; l.info = info;
  return l;
}
*/

inline bool operator==(const atom& x, const atom& y)
{
  return x.id == y.id && x.info == y.info;
}

inline bool operator!=(const atom& x, const atom& y)
{
  return x.id != y.id || x.info != y.info;
}

/*
inline atom operator~(const atom& l)
{
  return mk_atom(l.id^1, l.info);
}
*/


inline atom atom_undef(void) {
  return atom::undef();
  /*
  atom l;
  l.id = -1;
  l.info = 0;
  return l;
  */
}

/*
typedef struct {

} Atom_hash;
*/

/*
inline atom operator^(atom a, int x) {
  return atom(a.id^x, a.info);
}
*/

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
