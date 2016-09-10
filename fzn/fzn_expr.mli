(*  Representation of Flatzinc models *)

type ident = string

type fz_baseti =
  | Ti_bool
  | Ti_int
  | Ti_float

type baseval =
  | Ident of string
  | Int of int
  | Float of float

type lit =
  | Base of baseval
  | Set of baseval list
  | Array of baseval array

type expr =
  | Var of var
  | Lit of lit
  | Array of expr list

type ann_expr =
  | AE_var of var
  | AE_lit of lit
  | AE_array of ann_expr
  | AE_call of ident * (ann_expr list)
