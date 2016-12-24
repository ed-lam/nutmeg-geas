#include "utils/defs.h"
#include "solver/solver_data.h"
#include "solver/solver_debug.h"

namespace phage {

void check_pvals(solver_data* s) {
  pred_state& st(s->state);
  persistence& p(s->persist);    

  for(pid_t pi : irange(st.p_vals.size())) {
    if(st.p_vals[pi] != st.p_last[pi]) {
      if(!p.pred_touched[pi]) {
        fprintf(stderr, "Predicate [%d] (p%d%s) should be marked.\n",
          pi, pi>>1, pi&1 ? "-" : "+");
//        std::cerr << "Predicate [" << pi << "] should be marked." << std::endl;
        ERROR;
      }
    } else {
      if(p.pred_touched[pi]) {
        std::cerr << "Predicate [" << pi << "] should not be marked." << std::endl;
        ERROR;
      }
    }
  }
}

}
