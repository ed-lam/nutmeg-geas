#include "engine/branch.h"

Brancher::Brancher(env* _e)
  : e(_e)
{
  e->branchers.push(this);
}
