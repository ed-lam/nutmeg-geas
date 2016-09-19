#ifndef PHAGE_VALSET_H
#define PHAGE_VALSET_H
#include "solver/solver_data.h"

namespace phage {

// Mapping from pval_t to stuff.
// For small ranges, we just allocate an array.
// Otherwise, we use robin-hood hashing, and 
// resize when load factor hits 0.7.
enum mode_t { VS_Direct = 0, VS_Hash = 1, VS_Default };

template<class T>
class valmap_t {
public:
  enum { direct_lim = 500, cap_default = 281 };

  struct entry_t { pval_t key; unsigned int dist; T val; };

  valmap_t(pval_t _lb, pval_t _ub, mode_t _mode = VS_Default)
    : mode(_mode), lb(_lb), ub(_ub), count(0) {
      if(mode == VS_Default)
        mode = (ub - lb > direct_lim) ? VS_Hash : VS_Default;

      if(mode == VS_Direct) {
        cap = ub - lb;  
        data = (entry_t*) malloc(sizeof(entry_t)*cap);
      } else {
        cap = cap_default;
      }
      // For hash addressing, we leave a sentinel value at the end.
      data = (entry_t*) malloc(sizeof(entry_t)*(cap+mode));
      for(int ii : irange(cap+mode))
        data[ii] = { pval_err };
  }

  ~valmap_t(void) {
    free(data);
  }
  
  bool lookup(pval_t key, T& out);
  void insert(pval_t key, T val);
   
  size_t capacity(void) const { return cap; }
protected:  
  void insert_hash(pval_t key, T val);
  void resize_table(void);

  bool needs_resize(void) {
    return count > 0.7*cap;
  }

  mode_t mode; 
  pval_t lb;
  pval_t ub;

  entry_t* data;
  size_t cap;
  size_t count;
};

template<class T>
bool valmap_t<T>::lookup(pval_t key, T& out) {
  if(mode == VS_Direct) {
    if(data[key - lb].key == pval_err)
      return false;
    out = data[key - lb].val;
    return true;
  } else {
    // FIXME: Compute a proper hash
    unsigned int hash = key;
    entry_t* loc = data + (hash%cap);
    unsigned int dist = 0; // Distance from ideal

lookup_restart:
    while(loc->key != pval_err) {
      if(loc->key == key) {
        out = loc->val;
        return true;
      }
      if(loc->dist < dist)
        return false;
      ++dist;
      ++loc;
    }

    // This is why we have the sentinel value.
    if(loc == data + cap) {
      loc = data;
      goto lookup_restart;
    }

    return false;
  }
}

template<class T>
void valmap_t<T>::insert(pval_t key, T val) {
  if(mode == VS_Direct) {
    data[key - lb] = { key, 0, val };
  } else {
    if(needs_resize())
      resize_table();
    insert_hash(key, val);
  }
}

template<class T>
void valmap_t<T>::resize_table(void) {
  entry_t* old_data = data;
  size_t old_cap = cap;
  count = 0;

  // Insert and initialize the new values
  cap = cap*1.5;
  data = (entry_t*) malloc(sizeof(entry_t)*(cap+1));
  for(int ii : irange(cap+1))
    data[ii] = { pval_err };

  // Copy across the old values
  for(const entry_t& e : range(old_data, old_data + old_cap)) {
    if(e.val != pval_err)
      insert_hash(e.key, e.val);
  }

  // And free the data
  free(old_data);
}

template<class T>
inline void valmap_t<T>::insert_hash(pval_t key, T val) {
  unsigned int hash = key;
  entry_t* loc = data + (hash%cap);
  unsigned int dist = 0; // Distance from ideal

insert_restart:
  while(loc->key != pval_err) {
    if(loc->key == key) {
      loc->val = val;
      return;
    }

    // If the current element is closer to
    // its destination than we are, move it and
    // continue.
    if(loc->dist < dist) {
      std::swap(key, loc->key);
      std::swap(val, loc->val);
      std::swap(dist, loc->dist);
    }
    ++dist;
    ++loc;
  }

  if(loc == data+cap) {
    loc = data;
    goto insert_restart;
  }
  
  // Identified a free space 
  *loc = { key, dist, val };
  ++count;
}

};

#endif
