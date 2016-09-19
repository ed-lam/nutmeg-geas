#ifndef PHAGE_SOLVER_OPTIONS_H
#define PHAGE_SOLVER_OPTIONS_H

struct options {
  options(void)
    : learnt_dbmax(10000), learnt_growthrate(1.02),
      pred_act_inc(0.01), pred_act_growthrate(1.05),
      learnt_act_inc(0.01), learnt_act_growthrate(1.05)
  { } 
  
  int learnt_dbmax; 
  double learnt_growthrate;

  double pred_act_inc;
  double pred_act_growthrate; 

  double learnt_act_inc;
  double learnt_act_growthrate;
};

static const options default_options = options();

#endif
