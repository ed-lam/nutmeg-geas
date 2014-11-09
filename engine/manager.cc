#include "engine/manager.h"

LemmaManager::LemmaManager(env* _e)
  : e(_e), kind(_e->reg(this))
{ }
