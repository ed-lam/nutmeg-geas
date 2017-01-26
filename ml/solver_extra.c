#include <stddef.h>
#include <string.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/callback.h>
#ifdef Custom_tag
#include <caml/custom.h>
#include <caml/bigarray.h>
#endif
#include <caml/camlidlruntime.h>

#include "../solver/stats.h"
#include "../solver/options.h"
#include "../c/phage.h"

extern value camlidl_c2ml_atom_atom(atom *, camlidl_ctx _ctx);

CAMLprim value ml_get_conflict(value _s) {
  CAMLparam1 (_s);
  CAMLlocal2 (_at, _res);
  
  atom* arr;
  int sz;
  int ii; 
  
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;

  get_conflict(*((solver*) Data_custom_val(_s)), &arr, &sz);
  
  _res = caml_alloc(sz, 0);
  for(ii = 0; ii < sz; ii++) {
    _at = camlidl_c2ml_atom_atom(arr+ii, _ctx);
    Store_field(_res, ii, _at);
  }
  camlidl_free(_ctx);
  free(arr);
  CAMLreturn (_res);
}
