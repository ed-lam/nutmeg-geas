#ifndef PHAGE_BASE_TYPES_H__
#define PHAGE_BASE_TYPES_H__

typedef struct {
  char v;
} lbool;

static lbool mk_lbool(int v) { lbool l; l.v = v; return l; }
static lbool l_False = mk_lbool(-1);
static lbool l_True = mk_lbool(1);
static lbool l_Undef = mk_lbool(0);
inline lbool lbool_of_bool(bool b) {
  return mk_lbool(2*b - 1);
}

inline lbool operator~(lbool x) { return mk_lbool(-x.v); }
inline bool operator==(lbool x, lbool y) {
  return x.v == y.v;
}
inline bool operator!=(lbool x, lbool y) {
  return x.v != y.v;
}

// Concrete literals
/*
typedef struct {
  int x;
} lit;
static lit mk_lit(int v, bool sign) {
  lit l; l.x = v<<1|sign; return l;
}
*/

/*
template<class T>
class Watcher {
public:
  virtual void wakeup(T& v) = 0;
};
*/

class Watcher {
public:
  virtual void wakeup(int pid) = 0;

  class Info {
  public:
    Info(Watcher* _w, int _pid)
      : w(_w), pid(_pid)
    { }

    void operator()(void* origin) {
      if(w != origin) w->wakeup(pid);
    }
    
    Watcher* w;
    int pid;
  };
};

// Watcher for a given set of events.
template<class Event>
class WatcherT {
public:
  virtual void wakeup(int pid, Event& e) = 0;

  class Info {
  public:
    Info(WatcherT<Event>* _w, int _pid)
      : w(_w), pid(_pid)
    { }

    void operator()(Event& e, void* origin) {
      if(w != origin) w->wakeup(pid, e);
    }
    WatcherT<Event>* w;
    int pid;
  };
};
#endif
