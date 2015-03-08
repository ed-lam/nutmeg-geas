#ifndef __PHAGE_VTRAIL_H__
#define __PHAGE_VTRAIL_H__
#include <mtl/Vec.h>
#include <iostream>

namespace VTrail {
// Automatic trail handling, with constant-time
// access to prev_value and prev_level_value.

// Vector-backed implementation, which also
// permits O(log n) history checking.

// Assumption -- we're dealing with simple
// memory-copyable types.

enum TrailTags { T_CHANGED_PROP = 1, T_CHANGED_LEVEL = 2, T_CHANGED_ALL = 3 }; 

class _Trailed {
  public:
    _Trailed(unsigned int _t, unsigned int _lt)
      : time_stamp(_t), l_time_stamp(_lt)
    { }
    virtual void restore_to(int past_sz) = 0;

    unsigned int time_stamp;
    unsigned int l_time_stamp;
};

class Trail {
  class t_elt {
  public:
    t_elt(_Trailed* _ptr, int _sz)
      : ptr(_ptr), sz(_sz)
    { }
    _Trailed* ptr;
    int sz;
  };
public:
  Trail(void)
    : time(0), l_time(0)
  { }

  void tick(void)
  {
    // Make sure that time-stamps can't be
    // ignored long enough to overflow.
    if(registered.size() > 0)
    {
      registered[idx]->time_stamp = time;
      idx = (idx+1)%registered.size();
    }
    time++;
  }

  void push(_Trailed* t, int sz)
  {
    history.push(t_elt(t, sz)); 
  }
  void l_push(_Trailed* t, int sz)
  {
    l_history.push(t_elt(t, sz));
  }

  void tick_level(void)
  {
    if(registered.size() > 0)
    {
      registered[l_idx]->l_time_stamp = l_time;
      l_idx = (l_idx+1)%registered.size();
    }
    l_time++;
    l_hist_lim.push(l_history.size());
  }

  void restore_level(void)
  {
    int lim = l_hist_lim.last();
    l_hist_lim.pop();

    while(l_history.size() > lim)
    {
      undo(l_history.last());
      l_history.pop();
    }
  }

  void undo(t_elt& elt)
  {
    elt.ptr->restore_to(elt.sz);
  }

  int level(void) const { return l_hist_lim.size(); }

  void reg(_Trailed* t) { registered.push(t); }
protected:
  vec<_Trailed*> registered;

  // History entries for time-steps and levels.
  vec<t_elt> history;
  vec<t_elt> l_history;
  vec<int> l_hist_lim;
public:
  int time;
  int l_time;

protected:
  int idx;
  int l_idx;
};

template<class T>
class Trailed : public _Trailed {
public:
  Trailed<T>(Trail* _t, const T& _val)
    : _Trailed(_t->time-1, _t->l_time-1),
      elt(_val),
      t(_t)
  {
    _t->reg(this);
    history.push(_val);
  }

  Trailed<T>(const Trailed<T>& x)
    : _Trailed(x.t.time-1, x.t.l_time-1),
      elt(x.elt), t(x.t)
  {
    history.push(x.elt);
  }

  Trailed<T>& operator=(const Trailed<T>& x)
  {
    t = x.t;
    elt = x.elt;

    history.clear();
    history.push(x.elt);

    time_stamp = t->time-1;
    l_time_stamp = t->l_time-1;

    return *this;
  }

  Trailed<T>& operator=(const T& e)
  {
    std::cout << this << "," << t << "," << e << std::endl;

    if(time_stamp != t->time)
    {
      time_stamp = t->time;

      t->push(this, history.size());
      history.push(elt);

      if(l_time_stamp != t->l_time)
      {
        t->l_push(this, history.size());
      }
    }
    elt = e;

    return *this;
  }
  
  void restore_to(int past_sz)
  {
    assert(past_sz < history.size());
    elt = history[past_sz];
    history.shrink(history.size()-past_sz);
  }

  operator T() const { return elt; }

  T val(void) const {
    return elt;
  }

  T prev_val(void) const {
    assert(history.size() > 0);
    return history.last();
  }

protected:
  T elt;
  vec<T> history;
  Trail* t;

  unsigned int time_stamp;
  unsigned int l_time_stamp;
};

typedef Trailed<int> TrInt;

};
#endif
