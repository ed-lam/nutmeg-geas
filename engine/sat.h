#ifndef __PHAGE_SAT_H__
#define __PHAGE_SAT_H__

typedef struct {
  int x;
} lit;

inline lit mk_lit(int x, int sign) {
  lit l; l.x = (x<<1|sign); return l;
}

inline int lvar(lit& l) { return l.x<<1; }
inline int lsgn(lit& l) { return l.x&1; }

inline lit operator~(lit& l) {
  lit m = { l.x^1 };
  return m;
}

#endif
