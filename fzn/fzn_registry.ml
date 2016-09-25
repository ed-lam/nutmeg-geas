(* Constraint registry *)
module H = Hashtbl
type poster = (Solver.t -> Fzn_model.expr array -> bool)

exception Unknown_constraint of string

let post_table = H.create 17

let register id poster = H.add post_table id poster

let post solver id expr =
  try
    (H.find post_table id) solver expr
  with Not_found -> raise (Unknown_constraint id)

(* Some builtins *)
let not_yet solver args = failwith "Constraint not implemented."

let bool2int solver args = failwith "Implement me."

let init_builtins () =
  (* Standard Flatzinc predicates *)
  register "array_bool_and" not_yet ;
  register "array_bool_element" not_yet ;
  register "array_bool_or" not_yet ;
  register "array_bool_xor" not_yet ;
  register "array_int_element" not_yet ;
  register "array_var_bool_element" not_yet ;
  register "array_var_int_element" not_yet ;
  register "bool2int" bool2int ;
  register "bool_and" not_yet ;
  register "bool_clause" not_yet ;
  register "bool_eq" not_yet ;
  register "bool_eq_reif" not_yet ;
  register "bool_le" not_yet ;
  register "bool_le_reif" not_yet ;
  register "bool_lt" not_yet ;
  register "bool_lt_reif" not_yet ;
  register "bool_not" not_yet ;
  register "bool_or" not_yet ;
  register "bool_xor" not_yet ;

  register "bool_lin_eq" not_yet ;
  register "bool_lin_le" not_yet ;

  register "int_abs" not_yet ; (* |a| = b *)
  register "int_div" not_yet ; (* a/b = c, round towards zero *)

  register "int_eq" not_yet ;
  register "int_eq_reif" not_yet ;
  register "int_le" not_yet ;
  register "int_le_reif" not_yet ;
  register "int_lt" not_yet ;
  register "int_lt_reif" not_yet ;
  register "int_ne" not_yet ;
  register "int_ne_reif" not_yet ;

  register "int_lin_eq" not_yet ;
  register "int_lin_eq_reif" not_yet ;
  register "int_lin_le" not_yet ;
  register "int_lin_le_reif" not_yet ;
  register "int_lin_ne" not_yet ;
  register "int_lin_ne_reif" not_yet ;

  register "int_max" not_yet ;
  register "int_min" not_yet ;
  register "int_mod" not_yet ;
  register "int_plus" not_yet ;
  register "int_times" not_yet  (* a x b = c *)
