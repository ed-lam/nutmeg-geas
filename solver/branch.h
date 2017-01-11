#ifndef PHAGE_BRANCH_H
#define PHAGE_BRANCH_H
#include "engine/phage-types.h"
#include "engine/infer.h"

namespace phage {

class brancher {
public:
  virtual ~brancher(void) { }
  virtual patom_t branch(solver_data* s) = 0;
};

// Standard branchers
enum VarChoice { Var_InputOrder, Var_FirstFail, Var_Smallest, Var_Largest };
enum ValChoice { Val_Min, Val_Max, Val_Split, Val_Saved, Val_Default };

brancher* default_brancher(solver_data* s);
brancher* pred_act_branch(solver_data* s);
brancher* atom_act_branch(solver_data* s);

brancher* basic_brancher(VarChoice var_choice, ValChoice val_choice, vec<pid_t>& preds);
brancher* seq_brancher(vec<brancher*>& branchers);
brancher* limit_brancher(brancher* b);
  
patom_t branch(solver_data* s);

}
#endif
