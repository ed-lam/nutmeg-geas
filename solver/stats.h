#ifndef PHAGE_STATS_H
#define PHAGE_STATS_H

namespace phage {

struct statistics {
  statistics(void) : conflicts(0), restarts(0), solutions(0) { }
  int conflicts;
  int restarts;
  int solutions;
};

};

#endif
