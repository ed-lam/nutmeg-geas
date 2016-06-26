#ifndef PHAGE_ENV__H
#define PHAGE_ENV__H
#include <map>

class bool_var;
class int_var;
class float_var;

class var {
  friend class env;
  var(void) : impl(nullptr) { }
  var(void* ptr) : impl(ptr) { }
public:
  enum kind_t { Bool, Int, Float };

  virtual kind_t kind(void) = 0;  
  
  bool_var* get_bool(void) { return dynamic_cast<bool_var>(this); }
  int_var* get_int(void) { return dynamic_cast<int_var>(this); }
  float_var* get_float(void) { return dynamic_cast<float_var>(this); }

protected:
  void* impl;
};

typedef std::map<std::string, var*> var_map_t;

class env {
  env(void) : { }
     
};
#endif
