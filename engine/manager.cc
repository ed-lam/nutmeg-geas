#include "engine/manager.h"

AtomManager::AtomManager(env* _e)
  : e(_e), kind(_e->reg(this))
{ }
