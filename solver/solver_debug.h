#ifndef SOLVER_DEBUG_H
#define SOLVER_DEBUG_H
#include "solver/solver_data.h"

// #define CHECK_STATE
// #define LOG_ALL
// #define LOG_RESTART
// #define LOG_GC

#ifdef LOG_ALL

#ifndef LOG_RESTART
#define LOG_RESTART
#endif

#ifndef LOG_GC
#define LOG_GC
#endif

#endif

namespace phage {

void check_pvals(solver_data* s);

}
#endif
