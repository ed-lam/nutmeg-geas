#ifndef __PHAGE_LEMMA__
#define __PHAGE_LEMMA__
// Header file for atomic constraints.

// atom_kind indicates the appropriate handler
// for the atom.
// All atoms must be complementable.
typedef char atom_kind;
typedef int atom_id;
typedef int atom_val;

// Will need, eventually, to extend
// id and info to possible pointers.
typedef struct {
  atom_id id;      // Identify the sort of atom
  atom_val info;  // The atom's `value'
} atom_data;

typedef atom_data _atom;

typedef struct {
  atom_kind kind; // What manager handles this atom?
  _atom data;
} atom;

inline _atom mk_atom_(atom_id id, atom_val info) {
  _atom l; l.id = id; l.info = info;
  return l;
}
inline atom mk_atom(atom_kind kind, atom_id id, atom_val info) {
  atom l; l.kind = kind; l.data.id = id; l.data.info = info;
  return l;
}

inline atom operator~(const atom& l)
{
  return mk_atom(l.kind, l.data.id^1, l.data.info);
}

inline bool atom_sign(const atom& l)
{
  return (l.data.id&1) == 0;
}

inline atom atom_undef(void) {
  atom l;
  l.kind = -1;
  l.data.id = -1;
  l.data.info = 0;
  return l;
}
inline bool atom_is_undef(const atom& l) { return l.kind == -1; }

// Flag types
enum ResolvableT { R_NotResolvable, R_ResolveKeep, R_ResolveElim };

#endif
