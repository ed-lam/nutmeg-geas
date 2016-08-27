#include <utility>
#include <algorithm>
#include "engine/propagator.h"
#include "solver/solver_data.h"
#include "vars/intvar.h"

namespace phage {

typedef std::pair<int, int> ipair;

void int_element(solver_data* s, intvar x, intvar i, vec<int>& ys) {
  // Keep track of the landmarks
#if 1
  vec<ipair> incr;
  vec<ipair> decr;
  incr.push(ipair(0, ys[0]));
  decr.push(ipair(0, ys[0]));
  for(int ii : irange(1,ys.size())) {
    assert(incr.size() > 0);
    int y = ys[ii];
    while(incr.size() > 0) {
      ipair p = incr.last();
      if(p.second < y)
        break; 
      // How do we deal with equality
      incr.pop();
      if(p.second == y)
        break;
      if(incr.size() > 0) {
        add_clause(s, i <= incr.last().first, i >= ii, x >= p.second);
      } else {
        add_clause(s, i >= ii, x >= p.second);
      }
    }
    incr.push(ipair(ii, y));

    // Do the same for decreasing spans
    while(decr.size() > 0) {
      ipair p = decr.last();
      if(p.second > y)
        break;
      decr.pop();
      if(p.second == y)
        break;
      if(decr.size() > 0) {
        add_clause(s, i <= incr.last().first, i >= ii, x <= p.second);
      } else {
        add_clause(s, i >= ii, x <= p.second);
      }
    }
    decr.push(ipair(ii, y));
  }
  // incr is an increasing sequence of landmarks
  for(int ei : irange(1, incr.size())) {
    add_clause(s, x <= incr[ei-1].second, i >= incr[ei].first);
  }
  for(int ei : irange(1, decr.size())) {
    add_clause(s, i <= decr[ei-1].first, x <= decr[ei].second);
  }

  // Now punch any necessary holes in the domain of x.
  vec<int> ys_sort(ys);
  std::sort(ys_sort.begin(), ys_sort.end());
  for(int ii : irange(1, ys_sort.size())) {
    assert(ys_sort[ii-1] <= ys_sort[ii]);
    if(ys_sort[ii-1] + 1 < ys_sort[ii])
      add_clause(s, x <= ys_sort[ii-1], x >= ys_sort[ii]);
  }

  if(x.lb() < incr[0].second)
    x.set_lb(incr[0].second, reason());
  if(decr[0].second < x.ub())
    x.set_ub(decr[0].second, reason());
  if(i.lb() < 0)
    i.set_lb(0, reason());
  if(i.ub() > ys.size()-1)
    i.set_ub(ys.size()-1, reason());

#else
  bool inc = true;
  bool dec = true;
  for(int yi = 1; yi < ys.size(); yi++) {
    if(ys[yi-1] < ys[yi])
      dec = false;
    else if(ys[yi-1] > ys[yi])
      inc = false;
  }

  if(inc) {
    int jj = 0;
    do {
      int val(ys[jj]);
      int ii = jj;
      while(ii < ys.size() && ys[ii] == val)
        ii++;

      add_clause(s, i < jj, x >= val);
      add_clause(s, x < val, i >= jj);

      jj = ii;
    } while(jj < ys.size());
    i.set_lb(0, reason());
    i.set_ub(ys.size()-1, reason());
    if(x.lb() < ys[0])
      x.set_lb(ys[0], reason());
    if(ys.last() < x.ub())
      x.set_ub(ys.last(), reason());
  } else if (dec) {
    NOT_YET;
  } else {
    NOT_YET;
  }
#endif
  return;
}

void intvar_element(solver_data* s, intvar x, intvar i, vec<intvar>& ys) {
  NOT_YET;
  return; 
}
}
