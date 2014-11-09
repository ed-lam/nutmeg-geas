#ifndef __PHAGE_CHAIN_H__
#define __PHAGE_CHAIN_H__
#include <iostream>
#include "mtl/Vec.h"

// Data structure used for the quasi-literal chain
// Essentially a linked-list that supports constant-time backtracking.
class cn_ref {
public:
  cn_ref(int _level, int _idx) : level(_level), idx(_idx)
  { }

  int level;
  int idx;
};

template<class T>
class chain {
  typedef struct {
    T data;
    int prev;
    int next;
  } cnode;

public:
  chain() : nodes(), level(0)
  {
    nodes.push();

    cnode term;
    term.prev = 0;
    term.next = 1;
    nodes.last().push(term);
    nodes.last().push(term);
  }
  
  void pushLevel()
  {
    nodes.push();

    // Add terminal entries for the head and the tail.
    // Why? Saves checking for an empty chain on each push
    // or inject.
    // term.data is unspecified.
    cnode term;
    term.prev = 0;
    term.next = 1;
    nodes.last().push(term);
    nodes.last().push(term);

    level++;
  }

  void popLevel()
  {
    assert(level > 0);
    nodes.pop();
    level--;
  }

  T& get(const cn_ref& ref)
  {
    return nodes[ref.level][ref.idx].data;
  }

  cn_ref push(const T& data)
  {
    int id(nodes[level].size()); 

    int tail = nodes[level][1].prev;
    cnode fresh = {
      data,
      tail,
      1
    };
    nodes[level][tail].next = id;
    nodes[level][1].prev = id;
    nodes[level].push(fresh);

    cn_ref ref(level, id);
    return ref;
  }

  cn_ref inject_after(const cn_ref& target, T data)
  {
    int id(nodes[level].size());

    
    int prev = target.idx;
    int next = nodes[target.level][prev].next;
    cnode fresh = {
      data,
      prev,
      next
    };
    nodes[target.level][prev].next = id;
    nodes[target.level][next].prev = id;
    nodes[target.level].push(fresh);

    cn_ref ref(target.level, id);
    return ref;
  }
   
  // FIXME: This'll only work for chain<int>.
  void print(int level)
  {
    vec<cnode>& lnodes(nodes[level]);
    
    int idx = lnodes[0].next;
    int tail = 1;
    std::cout << "[";
    if(idx != tail)
    {
      std::cout << lnodes[idx].data;
      idx = lnodes[idx].next;
    }
    while(idx != tail)
    {
      std::cout << "," << lnodes[idx].data;
      idx = lnodes[idx].next;
    }
    std::cout << "]" << std::endl;
  }
protected:
  vec< vec<cnode> > nodes;
  
  int level;
};

#endif
