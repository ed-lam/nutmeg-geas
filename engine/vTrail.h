#ifndef __PHAGE_VTRAIL_H__
#define __PHAGE_VTRAIL_H__
#include <mtl/Vec.h>

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
    virtual void commit() = 0;
    virtual void finish_level() = 0;

    virtual void undo() = 0;
    virtual void pop_level() = 0;
};

class Trail {
public:
  Trail(void)
    : data_lim(), data(), changed_prop()
  { }

  void push_level(void)
  {
    // Clear the prop tags.
    assert(changed_prop.size() == 0);

    data_lim.push(data.size());
  }

  // Signal the end of an 'atomic' change.
  void commit(void)
  {
    for(int ii = 0; ii < changed_prop.size(); ii++)
      changed_prop[ii]->commit();
    changed_prop.clear();
  }
   
  void undo(void)
  {
    data.last()->undo();  
    data.pop();
  }

  void mark_changed(_Trailed* ptr)
  {
    changed_prop.push(ptr);
  }

  void mark_changed_level(_Trailed* ptr)
  {
    data.push(ptr);
  }

  void restore_level(void)
  {
    int lim = data_lim.last();
    data_lim.pop();      

    while(data.size() > lim)
      undo();
  }

  int level(void) const { return data_lim.size(); }

protected:
  // Data limit for a given level.
  vec<int> data_lim;
  vec<_Trailed*> data;

  vec<_Trailed*> changed_prop;
};

template<class T>
class Trailed : public _Trailed {
public:
  Trailed<T>(Trail* _t, const T& _val)
    : changed_level(0), changed_prop(0), elt(_val), t(_t)
  {

  }

  Trailed<T>(const Trailed<T>& x)
    : changed_level(x.changed_level),
      changed_prop(x.changed_prop),
      elt(x.elt),
      t(x.t)
   {
     x.history.copyTo(history);
   }

  Trailed<T>& operator=(const T& e)
  {
    if(!changed_prop)
    {
      changed_prop = 1;
      history.push(elt);
      t->mark_changed(this);
    }

    if(!changed_level)
    {
      changed_level = 1;
      history_lim.push(history.size());
      t->mark_changed_level(this);
    }

    // fprintf(stderr, "idx: %d\n", idx);
    elt = e;

    return *this;
  }
  
  void commit(void)
  {
    changed_prop = 0;
  }

  void finish_level(void)
  {
    changed_prop = 0;
    changed_level = 0;
  }

  void undo(void)
  {
    elt = history.last();
    history.pop();   
  }

  void pop_level(void)
  {
    int lim(history_lim.last());
    history_lim.pop();

    elt = history[lim];
    history.shrink(history.size() - lim + 1);
  }
  
  operator T() const { return elt; }

  T val(void) const {
    return elt;
  }

  T prev_val(void) const {
    return history.last();
  }
  T prev_level_val(void) const {
    return history[history_lim.last()];
  }

protected:
  int changed_level;
  int changed_prop;

  T elt;
  vec<T> history;
  vec<int> history_lim;
  Trail* t;
};

typedef Trailed<int> TrInt;

};
#endif
