#ifndef __PHAGE_TRAIL_H__
#define __PHAGE_TRAIL_H__
#include <mtl/Vec.h>

// Automatic trail handling, with constant-time
// access to prev_value and prev_level_value.

// Assumption -- we're dealing with simple
// memory-copyable types.

enum TrailTags { T_CHANGED_PROP = 1, T_CHANGED_LEVEL = 2, T_CHANGED_ALL = 3 }; 

// Voodoo to make sure there's enough space for either an
// int or a pointer.
typedef union {
  int* p;
  int v; 
} trail_elt;

inline trail_elt ptr_elt(int* p) { trail_elt e; e.p = p; return e; }
inline trail_elt val_elt(int v) { trail_elt e; e.v = v; return e; }
inline trail_elt flip_elt(int* p) {
  trail_elt e;
  e.p = (int*) (((uintptr_t) p)|1) ; return e;
}

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
      (*changed_prop[ii]) = 0;
    changed_prop.clear();
  }
   
  void save_word(int* word)
  {
    data.push(val_elt(*word));
    data.push(ptr_elt(word));
  }

  void save_flip(int* idx, int* word)
  {
    save_word(word);
    data.push(flip_elt(idx)); 
  }

  void restore(void)
  {
    int* ptr = data.last().p;
    data.pop();
     
    if(((intptr_t) ptr)&1)
    {
      // Flip entry.
      ptr = (int*) (((intptr_t) ptr)^1);
      (*ptr) ^= 1;
    } else {
      (*ptr) = data.last().v;  
      data.pop();
    }
  }

  void mark_changed(int* ptr)
  {
    changed_prop.push(ptr);
  }

  void restore_level(void)
  {
    int lim = data_lim.last();
    data_lim.pop();      

    while(data.size() > lim)
      restore();
  }

  int level(void) const { return data_lim.size(); }

protected:
  // Data limit for a given level.
  vec<int> data_lim;
  vec<trail_elt> data;

  vec<int*> changed_prop;
};

template<class T>
void save_raw(Trail* t, T* val)
{
  // We can chunk T up into a series of ints.
  assert(sizeof(T)%(sizeof(int)) == 0);

  int* val_intptr = static_cast<int*>(val);
  for(unsigned int ii = 0; ii < sizeof(T)/sizeof(int); ii++)
    t->save_word(val_intptr);
}

template<class T>
class Trailed {
public:
  Trailed<T>(Trail* _t, const T& _val)
    : changed_level(0), changed_prop(0), idx(0), t(_t)
  {
    // Initialize the default value.
    for(int ii = 0; ii < 3; ii++)
      elts[ii] = _val;
  }

  Trailed<T>& operator=(const T& val)
  {
    // fprintf(stderr,"Changed: %d; current: %d\n", changed_level, t->level());
    if(changed_level != t->level())
    {
      // Need to trail the value
      // at the end of the last level.
      save_raw(t, &(changed_level));
      changed_level = t->level();

      save_raw(t, &(elts[2]));
      elts[2] = elts[idx];
    }

    if(!(changed_prop))
    {
      idx ^= 1;
      t->save_flip(&idx, &(elts[idx]));
      t->mark_changed(&changed_prop);
      changed_prop = 1;
    }

    // fprintf(stderr, "idx: %d\n", idx);
    elts[idx] = val;

    return *this;
  }
  
  operator T() { return elts[idx]; }

  T val(void) const {
    return elts[idx];
  }
  T prev_val(void) const {
    return (changed_prop) ? elts[idx^1] : elts[idx];
  }
  T prev_level_val(void) const {
    // fprintf(stderr, "clev: %d, lev: %d, elts[2]: %d, elts[idx]: %d\n",
    //  changed_level, t->level(), elts[2], elts[idx]);
    return (changed_level == t->level()) ? elts[2] : elts[idx];
  }

protected:
  int changed_level;
  int changed_prop;
  int idx; 
  T elts[3];

  Trail* t;
};

typedef Trailed<int> TrInt;

#endif
