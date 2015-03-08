#ifndef __PHAGE_MAGIC_H__
#define __PHAGE_MAGIC_H__
// Magical templatey incantations for stuff.

template<>
class VaArgs
{
public:
  static int val = 0;
}

template<typename T, typename ... Ts>
class VaArgs
{
public:
  static int val = 1 + VaArgs<Ts ...>::val;
}

template<typename T>
inline void get_args(vec<T>& v) { }

template<typename T, typename ... Ts>
inline void get_args(vec<T>& v, T& elt, Ts ... args)
{
  v.push(elt);
  get_args(v, args); 
}
#endif
