(*  *)

(*
type kind =
  | Bool
  | Int
  | Float

type value =
  | BVal of bool
  | IVal of int
  | FVal of float
*)

type bool_var 
type int_var
type float_var

type solver 
type cstr
type model

val make_bool : solver -> bool_var
val make_int : solver -> (int, int) option -> int_var
val make_float : solver -> (float, float) option -> float_var

val bool_val : model -> bool_var -> bool
val int_val : model -> int_var -> int
val float_val : model -> float_var -> float

(* How do we represent expressions? *)
