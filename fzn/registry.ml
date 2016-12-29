(** Constraint registry *)
module H = Hashtbl
module Pr = Problem

module At = Atom
module B = Builtins
module S = Solver

type expr = (Solver.intvar, Atom.t) Problem.expr

type poster = Solver.t -> expr array -> Problem.ann_expr list -> bool

let registry = H.create 17

let register ident poster = H.add registry ident poster


let lookup ident = H.find registry ident

let bool_atom b = if b then Atom.at_True else Atom.neg Atom.at_True

let get_atom expr =
  match Pr.get_bval expr with
  | Pr.Bv_bool b -> bool_atom b
  | Pr.Bv_var at -> at

(* Is an expression an array with a given property? *)
let is_array p expr =
  match expr with
  | Pr.Arr es -> Array.fold_left (fun b x -> b && p x) true es
  | _ -> false
let is_int expr =
  match expr with
  | Pr.Ilit k -> true
  | _ -> false

let force_ivar solver expr =
  match expr with
  | Pr.Ilit x -> S.new_intvar solver x x
  | Pr.Ivar v -> v
  | _ -> failwith "Expected int-sorted value."

let ignore_constraint _ _ _ = true

let bool_clause solver args anns =
  let pos = Pr.get_array get_atom args.(0) in
  let neg = Pr.get_array (fun x -> Atom.neg (get_atom x)) args.(1) in
  Solver.post_clause solver (Array.append pos neg)

let int_max solver args anns =
  let x = Pr.get_ivar args.(0) in
  let y = Pr.get_ivar args.(1) in
  let z = Pr.get_ivar args.(2) in
  Builtins.int_max solver At.at_True z [|x; y|]

(*
let int_min solver args anns =
  let x = Pr.get_ivar args.(0) in
  let y = Pr.get_ivar args.(1) in
  let z = Pr.get_ivar args.(2) in
  Builtins.int_min solver At.at_True z [|x; y|]
 *)

let int_mul solver args anns =
  let x = Pr.get_ivar args.(0) in
  let y = Pr.get_ivar args.(1) in
  let z = Pr.get_ivar args.(2) in
  Builtins.int_mul solver At.at_True z x y

let int_lin_le solver args anns =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array Pr.get_ivar args.(1) in
  let terms = Array.init (Array.length xs)
                         (fun i -> { B.c = cs.(i) ; B.x = xs.(i) }) in
  let k = Pr.get_int args.(2) in
  Builtins.linear_le solver At.at_True terms k

let int_lin_ne solver args anns =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array Pr.get_ivar args.(1) in
  let terms = Array.init (Array.length xs)
                         (fun i -> { B.c = cs.(i) ; B.x = xs.(i) }) in
  let k = Pr.get_int args.(2) in
  Builtins.linear_ne solver At.at_True terms k


let int_lin_eq solver args anns =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array Pr.get_ivar args.(1) in
  let terms = Array.init (Array.length xs)
                         (fun i -> { B.c = cs.(i) ; B.x = xs.(i) }) in
  let negterms = Array.init (Array.length xs)
                            (fun i -> { B.c = -cs.(i) ; B.x = xs.(i) }) in
  let k = Pr.get_int args.(2) in
  (B.linear_le solver At.at_True terms k)
    && (B.linear_le solver At.at_True negterms (-k))

let bool2int solver args anns =
  let b = Pr.get_bvar args.(0) in
  let x = Pr.get_ivar args.(1) in
  (S.post_clause solver [|b ; S.ivar_le x 0|] &&
     S.post_clause solver [|At.neg b ; S.ivar_ge x 1|])
   
(* (x_1 /\ ... /\ x_n) <-> z *)
let array_bool_and solver args anns =
  let xs = Pr.get_array get_atom args.(0) in
  let z = get_atom args.(1) in
  Array.fold_left
    (fun b x -> b && S.post_clause solver [|At.neg z; x|])
    (S.post_clause solver
                   (Array.append [|z|] (Array.map At.neg xs))) xs

let array_bool_or solver args anns =
  let xs = Pr.get_array get_atom args.(0) in
  let z = get_atom args.(1) in
  Array.fold_left
    (* ~z -> ~x *)
    (fun b x -> b && S.post_clause solver [|z; At.neg x|])
    (* z -> x_1 \/ ... \/ x_n *)
    (S.post_clause solver (Array.append [|At.neg z|] xs)) xs

let array_int_element solver args anns =
  let idx = Pr.get_ivar args.(0) in
  let elts = Pr.get_array Pr.get_int args.(1) in
  let res = Pr.get_ivar args.(2) in
  B.int_element solver At.at_True res idx elts

let array_var_int_element solver args anns =
  let idx = Pr.get_ivar args.(0) in
  let res = Pr.get_ivar args.(2) in
  if is_array is_int args.(1) then
    let elts = Pr.get_array Pr.get_int args.(1) in
    B.int_element solver At.at_True res idx elts
  else 
    let elts = Pr.get_array (force_ivar solver) args.(1) in
    B.var_int_element solver At.at_True res idx elts
    (*
    (Format.fprintf Format.std_formatter "WARNING: var_int_element.@.";
     true)
    *)
 
let bool_iff solver x y =
  S.post_clause solver [|x ; At.neg y|]
  && S.post_clause solver [|At.neg x ; y|]

let int_eq solver args anns =
  let x = Pr.get_ivar args.(0) in
  let y = Pr.get_ivar args.(1) in
  B.int_le solver x y 0 && B.int_le solver y x 0

let int_eq_reif solver args anns =
  match Pr.get_bval args.(2) with
  | Pr.Bv_bool true -> int_eq solver args anns
  | Pr.Bv_bool false -> failwith "int_ne not implemented."
  | Pr.Bv_var r ->
  begin
    match Pr.get_ival args.(0), Pr.get_ival args.(1) with
    | Pr.Iv_int k1, Pr.Iv_int k2 -> k1 = k2
    | (Pr.Iv_var x, Pr.Iv_int k)
    | (Pr.Iv_int k, Pr.Iv_var x) ->
      let at = S.ivar_eq x k in
      bool_iff solver r at
    | Pr.Iv_var x, Pr.Iv_var y -> raise Util.Not_yet
  end

let int_ne_reif solver args anns =
  match Pr.get_bval args.(2) with
  | Pr.Bv_bool true -> raise Util.Not_yet
  | Pr.Bv_bool false -> int_eq solver args anns
  | Pr.Bv_var r ->
  begin
    match Pr.get_ival args.(0), Pr.get_ival args.(1) with
    | Pr.Iv_int k1, Pr.Iv_int k2 -> k1 <> k2
    | (Pr.Iv_var x, Pr.Iv_int k)
    | (Pr.Iv_int k, Pr.Iv_var x) ->
      let at = S.ivar_ne x k in
      bool_iff solver r at
    | Pr.Iv_var x, Pr.Iv_var y -> raise Util.Not_yet
  end

(*
let rec bool_sum_le_rec tbl solver idx xs k =
  try H.find tbl (idx, k)
  with Not_found ->
    if k < 0 then
      At.at_False
    else if idx = Array.length xs then
      At.at_True
    else
      let x = xs.(idx) in
      begin
      match x with
      | Pr.Bv_bool true -> bool_sum_le_rec tbl solver (idx+1) xs (k+1)
      | Pr.Bv_bool false -> bool_sum_le_rec tbl solver (idx+1) xs k
      | Pr.Bv_var b -> 
         let low = bool_sum_le_rec tbl solver (idx+1) xs (k+1) in
          let high = bool_sum_le_rec tbl solver (idx+1) xs k in
          let v = S.new_boolvar solver in
          H.add tbl (idx, k) v ;
          let _ = S.post_clause solver [|At.neg v ; low |] in
          let _ = S.post_clause solver [|At.neg v ; high ; At.neg b|] in
          v
       end
  
let bool_sum_le_base solver xs kv =
  let tbl = H.create 17 in
  let k = 
    match kv with
    | Pr.Iv_int k -> k
    | Pr.Iv_var x ->
       let sz = Array.length xs in
       H.add tbl (sz, 0) (At.at_True) ;
       for i = 1 to sz do
         H.add tbl (sz, i) (S.ivar_ge x i)
       done ;
       sz
    in S.post_atom solver (bool_sum_le_rec tbl solver 0 xs k)

let bool_sum_le solver args anns =
  let xs = Pr.get_array Pr.get_bval args.(0) in
  let kv = Pr.get_ival args.(1) in
  bool_sum_le_base solver xs kv

let bool_sum_ge_base solver xs kv =
  let k = 
    match kv with
    | Pr.Iv_int k -> k
    | Pr.Iv_var x ->
       let sz = Array.length xs in
       H.add tbl (sz, 0) (At.at_True) ;
       for i = 1 to sz do
         H.add tbl (sz, i) (S.ivar_ge x i)
       done ;
       sz
    in S.post_atom solver (bool_sum_le_rec tbl solver 0 xs k)
  
let bool_sum_ge solver args anns =
  let xs = Pr.get_array Pr.get_bval args.(0) in
  let kv = Pr.get_ival args.(1) in
  bool_sum_ge_base solver xs kv
  *)

(* Maybe separate this out into a separate
 * per-solver registrar *)
let initialize () =
  let handlers =
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
     (* "bool_sum_le", bool_sum_le ; *)
     "array_int_element", array_int_element ; 
     "array_var_int_element", array_var_int_element ; 
     (*
     "array_var_int_element", array_var_int_element *) ] in
  List.iter (fun (id, handler) ->
             register id handler) handlers

  
