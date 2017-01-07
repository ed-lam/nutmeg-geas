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

let array_int_max solver args anns =
  let xs = Pr.get_array Pr.get_ivar args.(0) in
  let z = Pr.get_ivar args.(1) in
  Builtins.int_max solver At.at_True z xs
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

(* Specialization of linear inequalities *)
let simplify_linterms terms k =
  let rec aux acc k' ts =
    match ts with
    | [] -> (List.rev acc), k' 
    | (0, _) :: ts' -> aux acc k' ts'
    | (c, Pr.Ilit x) :: ts' -> aux acc (k' - c*x)  ts'
    | (c, Pr.Ivar v) :: ts' -> aux ((c, v) :: acc) k' ts'
    | _ -> failwith "Expected integer-typed operands to linear."
  in
  aux [] k (Array.to_list terms)

(* Specialized int_lin_le *)
let post_lin_le solver cs xs k =
   let terms = Array.init (Array.length xs) (fun i -> cs.(i), xs.(i)) in
  match simplify_linterms terms k with
  | [], k -> 0 <= k
    (* GKG: Check for rounding *)
  | [c, x], k ->
    if c < 0 then
      S.post_atom solver (S.ivar_ge x ((-k)/(-c)))
    else
      S.post_atom solver (S.ivar_le x (k/c))
  | [1, x; -1, y], k | [-1, y; 1, x], k ->
    B.int_le solver At.at_True x y k
  | ts, k ->
    B.linear_le
      solver At.at_True
      (Array.map (fun (c, x) -> {B.c = c ; B.x = x}) (Array.of_list ts)) k
 
let int_lin_le solver args anns =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array (fun x -> x) args.(1) in
  let k = Pr.get_int args.(2) in
  post_lin_le solver cs xs k

  (*
  let terms = Array.init (Array.length xs) (fun i -> cs.(i), xs.(i)) in
  match simplify_linterms terms k with
  | [], k -> 0 <= k
    (* GKG: Check for rounding *)
  | [c, x], k ->
    if c < 0 then
      S.post_atom solver (S.ivar_ge x ((-k)/(-c)))
    else
      S.post_atom solver (S.ivar_le x (k/c))
  | [1, x; -1, y], k | [-1, y; 1, x], k ->
    B.int_le solver At.at_True x y k
  | ts, k ->
    B.linear_le
      solver At.at_True
      (Array.map (fun (c, x) -> {B.c = c ; B.x = x}) (Array.of_list ts)) k
      *)

(* Specialized int_lin_le *)
let post_lin_le_reif s cs xs k r =
  match r with
  | Pr.Blit true -> post_lin_le s cs xs k
  | Pr.Blit false -> post_lin_le s (Array.map ((-) 0) cs) xs (1-k)
  | Pr.Bvar r ->
  begin
    let terms = Array.init (Array.length xs) (fun i -> cs.(i), xs.(i)) in
    match simplify_linterms terms k with
    | [], k -> S.post_atom s (if 0 <= k then r else At.neg r)
    | [c, x], k ->
      let bnd = if c < 0 then ((-k)/(-c)) else k/c in
      S.post_clause s [|At.neg r; S.ivar_ge x bnd|]
      && S.post_clause s [|r; S.ivar_lt x bnd|]
    | [1, x; -1, y], k | [-1, y; 1, x], k ->
      B.int_le s r x y k
      && B.int_le s (At.neg r) y x (-k-1)
    | ts, k ->
      B.linear_le
        s r (Array.map (fun (c, x) -> {B.c = c ; B.x = x}) (Array.of_list ts)) k
        && B.linear_le
             s (At.neg r) (Array.map (fun (c, x) -> {B.c = -c; B.x = x}) (Array.of_list ts)) (-k-1)
  end
  | _ -> failwith "Expected bool-sorted value in int_lin_le_reif."

let int_lin_le_reif solver args anns =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array (fun x -> x) args.(1) in
  let k = Pr.get_int args.(2) in
  post_lin_le_reif solver cs xs k args.(3)
  (*
  let terms = Array.init (Array.length xs) (fun i -> cs.(i), xs.(i)) in
  match simplify_linterms terms k with
  | [], k -> 0 <= k
    (* GKG: Check for rounding *)
  | [c, x], k ->
    if c < 0 then
      S.post_atom solver (S.ivar_ge x ((-k)/(-c)))
    else
      S.post_atom solver (S.ivar_le x (k/c))
  | [1, x; -1, y], k | [-1, y; 1, x], k ->
    B.int_le solver At.at_True x y k
  | ts, k ->
    B.linear_le
      solver At.at_True
      (Array.map (fun (c, x) -> {B.c = c ; B.x = x}) (Array.of_list ts)) k
      *)


let int_lin_ne solver args anns =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array (force_ivar solver) args.(1) in
  let terms = Array.init (Array.length xs)
                         (fun i -> { B.c = cs.(i) ; B.x = xs.(i) }) in
  let k = Pr.get_int args.(2) in
  Builtins.linear_ne solver At.at_True terms k


(*
let int_lin_eq solver args anns =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array (force_ivar solver) args.(1) in
  let terms = Array.init (Array.length xs)
                         (fun i -> { B.c = cs.(i) ; B.x = xs.(i) }) in
  let negterms = Array.init (Array.length xs)
                            (fun i -> { B.c = -cs.(i) ; B.x = xs.(i) }) in
  let k = Pr.get_int args.(2) in
  (B.linear_le solver At.at_True terms k)
    && (B.linear_le solver At.at_True negterms (-k))
    *)
(* Specialized int_lin_eq *)
let int_lin_eq solver args anns =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array (fun x -> x) args.(1) in
  let k = Pr.get_int args.(2) in
  let terms = Array.init (Array.length xs) (fun i -> cs.(i), xs.(i)) in
  match simplify_linterms terms k with
  | [], k -> 0 = k
    (* GKG: Check for rounding *)
  | [c, x], k ->
    if k mod c = 0 then
      S.post_atom solver (S.ivar_eq x (k/c))
    else
      false
  | [1, x; -1, y], k | [-1, y; 1, x], k ->
    B.int_le solver At.at_True x y k
      && B.int_le solver At.at_True y x (-k)
  | ts, k ->
    let t_arr = Array.of_list ts in
    let pos = Array.map (fun (c, x) -> { B.c = c; B.x = x}) t_arr in
    let neg = Array.map (fun (c, x) -> { B.c = -c; B.x = x}) t_arr in
    B.linear_le solver At.at_True pos k
      && B.linear_le solver At.at_True neg (-k)

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
  let idx = (force_ivar solver) args.(0) in
  let elts = Pr.get_array Pr.get_int args.(1) in
  let res = (force_ivar solver) args.(2) in
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
  match args.(0), args.(1) with
  | Pr.Ivar x, Pr.Ivar y ->
    B.int_le solver At.at_True x y 0 && B.int_le solver At.at_True y x 0
  | Pr.Ilit c, Pr.Ivar x | Pr.Ivar x, Pr.Ilit c ->
    S.post_atom solver (S.ivar_le x c) && S.post_atom solver (S.ivar_ge x c)
  | Pr.Ilit c1, Pr.Ilit c2 -> c1 = c2
  | _, _ -> failwith "int_eq expects int operands."

let int_le solver args anns =
  match args.(0), args.(1) with
  | Pr.Ivar x, Pr.Ivar y -> B.int_le solver At.at_True x y 0
  | Pr.Ivar x, Pr.Ilit c -> S.post_atom solver (S.ivar_le x c)
  | Pr.Ilit c, Pr.Ivar x -> S.post_atom solver (S.ivar_ge x c)
  | Pr.Ilit c1, Pr.Ilit c2 -> c1 <= c2
  | _, _ -> failwith "int_le expects int operands."

(*
let int_le solver args anns =
  let x = (force_ivar solver) args.(0) in
  let y = (force_ivar solver) args.(1) in
  B.int_le solver At.at_True x y 0
  *)

let int_lt solver args anns =
  match args.(0), args.(1) with
  | Pr.Ivar x, Pr.Ivar y -> B.int_le solver At.at_True x y (-1)
  | Pr.Ivar x, Pr.Ilit c -> S.post_atom solver (S.ivar_lt x c)
  | Pr.Ilit c, Pr.Ivar x -> S.post_atom solver (S.ivar_gt x c)
  | Pr.Ilit c1, Pr.Ilit c2 -> c1 < c2
  | _, _ -> failwith "int_le expects int operands."

(*
let int_lt solver args anns =
  let x = (force_ivar solver) args.(0) in
  let y = (force_ivar solver) args.(1) in
  B.int_le solver At.at_True x y 1
  *)

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
     "maximum", array_int_max ;
     (* "int_min", int_min ; *)
     "int_times", int_mul ;
     "int_lin_le", int_lin_le ;
     "int_lin_le_reif", int_lin_le_reif ;
     "int_lin_eq", int_lin_eq ;
     "int_lin_ne", int_lin_ne ;
     (* "int_lin_ne", ignore_constraint ; *)
     "int_eq", int_eq ;
     "int_le", int_le ;
     "int_lt", int_lt ;
     (* "int_ne", int_ne ; *)
     (* "int_le_reif", int_le_reif ; *)
     "int_eq_reif", int_eq_reif ;
     "int_ne_reif", int_ne_reif ;
     "bool2int", bool2int ;
     "array_bool_and", array_bool_and ;
     "array_bool_or", array_bool_or ;
     (* "bool_sum_le", bool_sum_le ; *)
     "array_int_element", array_int_element ; 
     "array_var_int_element", array_var_int_element ;
      ] in
  List.iter (fun (id, handler) ->
             register id handler) handlers
