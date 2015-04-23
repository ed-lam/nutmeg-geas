#ifndef __PHAGE_LINEAR_H__
#define __PHAGE_LINEAR_H__

#include "engine/base-types.h"
#include "engine/propagator.h"
#include "vars/var-interface.h"

template<class Host, class V, class Cst>
class LinearLE : public Propagator<Host>, public WatcherT<char>
{
//  typedef NumVar<V, Cst> var_t;
  typedef LinearLE<Host,V,Cst> lin_le_t;

public:

  LinearLE(Host* _h, vec<Cst>& coeffs, vec<V>& vs, Cst _c)
    : Propagator<Host>(_h), h(_h), c(_c)
  {
    assert(coeffs.size() == vs.size());
    for(int vi = 0; vi < vs.size(); vi++)
    {
      IntVar v = vs[vi];
      if(coeffs[vi] > 0)
      {
        v.add_watch((WatcherT<char>*) this, xs.size()<<1, IVE_LB);
        xs.push(v);
        x_coeffs.push(coeffs[vi]);
      } else if(coeffs[vi] < 0) {
        v.add_watch((WatcherT<char>*) this, ys.size()<<1|1, IVE_UB);
        ys.push(v);
        y_coeffs.push(-coeffs[vi]);
      }
    }
    ((Propagator<Host>*) this)->enqueue();
  }

  // 
  void wakeup(int _l, char& evt)
  {
    ((Propagator<Host>*) this)->enqueue();
  }

  void _cleanup(void)
  {
    
  }

  static void explain(void* p_ptr, expl_cookie cookie, vec<atom>& out_expl)
  {
    lin_le_t* ptr = ((lin_le_t*) p_ptr);
    if(cookie&1)
    {
      ptr->explain_y(cookie>>1, out_expl);
    } else {
      ptr->explain_x(cookie>>1, out_expl);
    }
  }

  void explain_x(int xi, vec<atom>& out_expl)
  {
    assert(0 && "LinearLE::explain_x not implemented.");
    return;
  }
  void explain_y(int xi, vec<atom>& out_expl)
  {
    assert(0 && "LinearLE::explain_y not implemented.");
    return;
  }

  expln make_reason_x(int xi) {
    return expln(explain, this, (expl_cookie) xi<<1);
  }
  expln make_reason_y(int yi) {
    return expln(explain, this, (expl_cookie) (yi<<1|1));
  }
 
  bool propagate(vec<atom>& confl)
  {
    printf("Propagating linear-le.\n");
    
    Cst slack = c;

    // Compute the lower bound
    for(int xi = 0; xi < xs.size(); xi++)
      slack -= x_coeffs[xi]*lb(xs[xi]);
     
    for(int yi = 0; yi < ys.size(); yi++)
      slack += y_coeffs[yi]*ub(ys[yi]);
     
    if(slack < 0)
    {
      printf(" ...conflict.\n");
      return false;
    }

    // Propagate bounds
    for(int xi = 0; xi < xs.size(); xi++)
    {
      Cst x_ub = lb(xs[xi]) + (slack/x_coeffs[xi]);
      if(x_ub < ub(xs[xi]))
      {
        h->post(xs[xi].le(x_ub), make_reason_x(xi), this);
      }
    }
    for(int yi = 0; yi < ys.size(); yi++)
    {
      Cst y_lb = ub(ys[yi]) - (slack/y_coeffs[yi]);
      if(lb(ys[yi]) < y_lb)
      {
        h->post(ys[yi].ge(y_lb), make_reason_y(yi), this);
      }
    }

    printf(" ...done.\n");
    return true;
  }

  void explain_inf(lit l, vec<atom>& out_expl)
  {
    assert(0 && "linear-le::explain_inf not yet implemented."); 
  }

  Host* h;

  vec<Cst> x_coeffs;
  vec<V> xs;

  vec<Cst> y_coeffs;
  vec<V> ys;

  Cst c;
};

#endif
