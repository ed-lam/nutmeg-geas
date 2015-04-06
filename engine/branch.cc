#include "engine/branch.h"

Brancher::Brancher(env* _e)
{
  _e->branchers.push(this);
}
