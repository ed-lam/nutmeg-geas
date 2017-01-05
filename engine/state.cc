#include "engine/state.h"
#include "vars/intvar.h"

namespace phage {

void log_state(pred_state& p) {
  int pi = 0;
  fprintf(stderr, "~~~~~~~~~~~~~~~\n");
  for(int ii = 0; ii < p.p_vals.size(); pi++, ii += 2) {
    fprintf(stderr, "p%d : [%lld, %lld]\n",
    // fprintf(stderr, "p%d : [%d, %d]\n",
      pi, to_int(p.p_vals[ii]), to_int(pval_max - p.p_vals[ii+1]));
  }
  fprintf(stderr, "~~~~~~~~~~~~~~~\n");
}

}
