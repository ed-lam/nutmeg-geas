#ifndef __PHAGE_BRANCH_H__
#define __PHAGE_BRANCH_H__

class Brancher;

#include "engine/atom.h"
#include "engine/env.h"

class Brancher {
public:
  Brancher(env* e);

  virtual atom branch(void) = 0;
};

#endif
