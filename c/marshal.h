#ifndef PHAGE_C_MARSHAL_H
#define PHAGE_C_MARSHAL_H
#include "solver/solver.h"
#include "solver/model.h"
#include "c/atom.h"
#include "c/phage.h"

inline phage::solver* get_solver(solver s) {
  return (phage::solver*) s;
}
inline phage::intvar* get_intvar(intvar v) {
  return (phage::intvar*) v;
}
inline phage::patom_t get_atom(atom at) {
  return phage::patom_t(at.pid, at.val);
}
inline atom unget_atom(phage::patom_t at) {
  atom a = { at.pid, at.val };
  return a;
}

inline phage::model* get_model(model m) {
  return (phage::model*) m;
}

inline phage::brancher* get_brancher(brancher b) {
  return (phage::brancher*) b;
}

inline result unget_result(phage::solver::result r) {
  switch(r) {
    case phage::solver::SAT:
      return SAT;
    case phage::solver::UNSAT:
      return UNSAT;
    case phage::solver::UNKNOWN:
    default:
      return UNKNOWN;
  }
}

#endif
