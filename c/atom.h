#ifndef PHAGE_C_ATOM_H
#define PHAGE_C_ATOM_H
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
  uint32_t pid;
  uint64_t val;
  // uint32_t val;
} atom;

typedef uint32_t pred_t;

atom neg(atom);

#ifdef __cplusplus
}
#endif

#endif
