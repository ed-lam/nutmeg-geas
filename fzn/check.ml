(* Check that a model is actually a solution. *)
module Dy = DynArray
module H = Hashtbl

module Pr = Problem
module Sol = Solver

exception Not_satisfied of string
exception No_checker of string

(* Evaluate an expression under a model.
 * - FIXME: Duplicated from fzn_phage.ml. *)
let rec eval_expr model ivars bvars expr =
  match expr with
  | Pr.Ilit v -> Pr.Ilit v
  | Pr.Ivar iv -> Pr.Ilit (Sol.int_value model ivars.(iv))
  | Pr.Blit b -> Pr.Blit b
  | Pr.Bvar bv -> Pr.Blit (Sol.atom_value model bvars.(bv))
  | Pr.Set dom -> Pr.Set dom
  | Pr.Arr es -> Pr.Arr (Array.map (eval_expr model ivars bvars) es)

let rec print_sol fmt expr =
  match expr with
  | Pr.Ilit v -> Format.pp_print_int fmt v
  | Pr.Blit b -> Format.pp_print_string fmt (if b then "true" else "false")
  | Pr.Arr es -> Util.print_array print_sol fmt es
  | _ -> ()

let checkers = H.create 17

let check prob ivars bvars model =
  try
    let _ = Dy.index_of (fun ((id, args), ann) ->
      try
        let check_fun = H.find checkers id in
        not (check_fun (Array.map (eval_expr model ivars bvars) args))
      with Not_found -> raise (No_checker id)) prob.Pr.constraints
    in false
  with Not_found -> true

let check_exn prob ivars bvars model =
  Dy.iter (fun ((id, args), ann) ->
    let check_fun = H.find checkers id in
    let vals = Array.map (eval_expr model ivars bvars) args in
    if not (check_fun vals) then
      begin
        (if !Opts.verbosity > 1 then
          (Util.print_array print_sol Format.err_formatter vals ;
          Format.fprintf Format.err_formatter "@.")) ;
        raise (Not_satisfied id)
      end
    else
      ()) prob.Pr.constraints

let array_int_element args =
  let elts = Pr.get_array Pr.get_int args.(1) in
  let x = Pr.get_int args.(0) in
  let z = Pr.get_int args.(2) in
  1 <= x && x <= Array.length elts &&
  z = elts.(x-1)

let int_linear_rel rel args =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array Pr.get_int args.(1) in
  let k = Pr.get_int args.(2) in
  let vs = Array.init (Array.length xs) (fun i -> cs.(i) * xs.(i)) in
  rel (Array.fold_left (+) 0 vs) k

(* Initialize the checkers *)
let check_funs =
(*
    ["bool_clause", bool_clause ;
     "int_max", int_max ;
     (* "int_min", int_min ; *)
     "int_times", int_mul ;
     "int_lin_le", int_lin_le ;
     "int_lin_eq", int_lin_eq ;
     "int_lin_ne", int_lin_ne ;
     (* "int_lin_ne", ignore_constraint ; *)
     "int_eq", int_eq ;
     (* "int_ne", int_ne ; *)
     "int_eq_reif", int_eq_reif ;
     "int_ne_reif", int_ne_reif ;
     "bool2int", bool2int ;
     "array_bool_and", array_bool_and ;
     "array_bool_or", array_bool_or ;
     (* "bool_sum_le", bool_sum_le ; *) *)
     [ "int_lin_le", int_linear_rel (<=) ;
       "int_lin_ne", int_linear_rel (<>);
       "int_lin_eq", int_linear_rel (=) ;
       "array_int_element", array_int_element ; 
       "array_var_int_element", array_int_element ; 
     ]
let init () =
  List.iter (fun (id, checker) -> H.add checkers id checker) check_funs


let _ = init ()
