#ifndef __PERM_SPARSE_SET_H__
#define __PERM_SPARSE_SET_H__

#include <cassert>
#include <cstdlib>

// Variant of sparse set, which preserves sparse as a permutation
// of 1..n.
// Cheaper lookups, slightly more expensive modifications

class p_sparseset {
  enum { dom_default = 10 };
public:
   p_sparseset(void)
     : dom(dom_default),
       sz( 0 ),
       sparse((unsigned int*) malloc(dom*sizeof(unsigned int))),
       dense((unsigned int*) malloc(dom*sizeof(unsigned int)))
   {
      for(unsigned int ii = 0; ii < dom; ii++) {
        sparse[ii] = ii;
        dense[ii] = ii;
      }
   }

   p_sparseset(unsigned int size) : dom(size),
      sz( 0 ),
      sparse((unsigned int*) malloc(size*sizeof(unsigned int))),
      dense((unsigned int*) malloc(size*sizeof(unsigned int)))
   {
      for(unsigned int ii = 0; ii < dom; ii++) {
        sparse[ii] = ii;
        dense[ii] = ii;
      }
   }

   ~p_sparseset() {
      if( sparse )
         free(sparse);
      if( dense )
         free(dense);  
   }

   unsigned int* begin(void) { return dense; }
   unsigned int* end(void) { return dense+sz; }

   inline bool elem(unsigned int value) const {
     return sparse[value] < sz;
   }
   
   bool insert(unsigned int value) {
//      assert( !elem(value) );

      unsigned int repl = dense[sz];
      unsigned int r_idx = sparse[value];

      dense[r_idx] = repl;
      sparse[repl] = r_idx;

      sparse[value] = sz;
      dense[sz] = value;
      sz++;
      
      return true;
   }

   void remove(unsigned int value) {
//     if(!elem(value))
//       return;
     unsigned int pos = sparse[value];

     sz--;
     unsigned int replacement = dense[sz];

     sparse[replacement] = pos;
     dense[pos] = replacement;

     sparse[value] = sz;
     dense[sz] = value;
   }
   
   void clear(void) {
      sz = 0;
   }

   unsigned int pos(unsigned int val) const
   {
      assert( elem(val) );
      return sparse[val];
   }
    
   unsigned int operator [] (unsigned int index) {
      assert(index < dom);
      return dense[index];
   }
    
   void growTo(unsigned int new_dom)
   {
      if( dom <= new_dom )
      {
        unsigned int old_dom = dom;
        while(dom <= new_dom)
          dom *= 1.5;
        // Of course, this is bad practice -- should check the return value
        sparse = (unsigned int*) realloc(sparse,sizeof(unsigned int)*dom); 
        dense = (unsigned int*) realloc(dense,sizeof(unsigned int)*dom);

        // Initialize the newly added elements
        for(; old_dom < dom; old_dom++) {
          sparse[old_dom] = old_dom;
          dense[old_dom] = old_dom;
        }
      }
   }

   unsigned int size(void) {
      return sz;
   }
   
   unsigned int domain(void) {
      return dom;
   }
       
   unsigned int dom;
   unsigned int sz;
protected:
   unsigned int* sparse;
   unsigned int* dense;
};

#endif
