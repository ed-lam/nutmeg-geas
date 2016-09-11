#ifndef PHAGE_C_ATOM_H
#define PHAGE_C_ATOM_H
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
  uint32_t pid;
  uint64_t val;
} atom;

atom neg(atom);
//atom at_true(void);

#ifdef __cplusplus
}
#endif

#endif
