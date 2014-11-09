#ifndef __PHAGE_LEMMA__
#define __PHAGE_LEMMA__
// Header file for lemmas.

// lem_kind indicates the appropriate handler
// for the lemma.
// All lemmas must be complementable.
typedef char lem_kind;
typedef int lem_id;
typedef int lem_val;

// Will need, eventually, to extend
// id and info to possible pointers.
typedef struct {
  lem_id id;      // Identify the sort of lemma
  lem_val info;  // The lemma's `value'
} lem_data;

typedef lem_data _lemma;

typedef struct {
  lem_kind kind; // What manager handles this lemma?
  _lemma data;
} lemma;

inline _lemma mk_lem_(lem_id id, lem_val info) {
  _lemma l; l.id = id; l.info = info;
  return l;
}
inline lemma mk_lem(lem_kind kind, lem_id id, lem_val info) {
  lemma l; l.kind = kind; l.data.id = id; l.data.info = info;
  return l;
}

inline lemma operator~(const lemma& l)
{
  return mk_lem(l.kind, l.data.id^1, l.data.info);
}

inline bool lem_sign(const lemma& l)
{
  return (l.data.id&1) == 0;
}

inline lemma lem_undef(void) {
  lemma l;
  l.kind = -1;
  l.data.id = -1;
  l.data.info = 0;
  return l;
}
inline bool lem_is_undef(const lemma& l) { return l.kind == -1; }

// Flag types
enum ResolvableT { R_NotResolvable, R_ResolveKeep, R_ResolveElim };

#endif
