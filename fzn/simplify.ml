(** Problem simplification *)
(* Not doing full EUF-style congruence closure -- 
 * just simple aliasing.
 * TODO: Add structural hashing. *)
module H = Hashtbl
module Dy = DynArray

module Pr = Problem

type bval_id = int
type ival_id = int

type kind = 
  | Bool
  | Int of Dom.t
type irel = Ile | Ieq | Igt | Ine

type idef = 
  | Iv_none
  | Iv_const of int
  (* Aliasing *)
  | Iv_eq of ival_id
  | Iv_opp of ival_id
  (* Arithmetic functions *)
  | Iv_sum of ival_id array
  | Iv_prod of ival_id array
  | Iv_max of ival_id array
  | Iv_min of ival_id array
  | Iv_b2i of bval_id

type bdef =
  | Bv_none
  | Bv_const of bool
  | Bv_eq of Problem.bval_id
  | Bv_neg of Problem.bval_id
  | At of Problem.ival_id * irel * int
  | Bv_or of bval_id array
  | Bv_and of bval_id array

type t = ((idef array) * (bdef array) * Problem.t)

let irel_neg = function
  | Ile -> Igt
  | Igt -> Ile
  | Ieq -> Ine
  | Ine -> Ieq

let rel_str = function
  | Ile -> "<="
  | Igt -> ">"
  | Ieq -> "="
  | Ine -> "!="

let fzn_irel rel x y =
  match rel with
  | Ile -> (("int_le", [|x; y|]), [])
  | Igt -> (("int_lt", [|y; x|]), [])
  | Ieq -> (("int_eq", [|x; y|]), [])
  | Ine -> (("int_ne", [|x; y|]), [])

let fzn_irel_reif rel r x y =
  match r with
  | Pr.Blit true -> fzn_irel rel x y
  | Pr.Blit false -> fzn_irel (irel_neg rel) x y
  | _ -> 
    match rel with
    | Ile -> (("int_le_reif", [|x; y; r|]), [])
    | Igt -> (("int_lt_reif", [|y; x; r|]), [])
    | Ieq -> (("int_eq_reif", [|x; y; r|]), [])
    | Ine -> (("int_ne_reif", [|x; y; r|]), [])
  
(*
type bdef =
  (* | Bconst of bool *)
  | Beq of Problem.bval_id
  | Bneg of Problem.bval_id
  | At of Problem.ival_id * irel * int
  *)

(*
let bdef_neg = function
  (* | Bconst b -> Bconst (not b) *)
  | Def_eq p -> Def_bne p
  | Bneg p -> Beq p
  | At (x, r, k) -> At (x, irel_neg r, k)
  *)

type state = {
  idefs : idef array ;
  bdefs : bdef array ;
  cons : (Pr.cstr * Pr.ann_expr list) Dy.t
}

let registry = H.create 17

let init_state pr =
  { idefs = Array.make (Dy.length pr.Pr.ivals) Iv_none ;
    bdefs = Array.make (Dy.length pr.Pr.bvals) Bv_none ;
    cons = Dy.create () }


(* Dealing with signed union-find stuff *)
(* Neg should only appear with Bool-kind values *)
type 'a rep =
  | Pos of 'a
  | Neg of 'a
let neg_rep = function
  | Pos v -> Neg v
  | Neg v -> Pos v

let bdef_of_rep = function
  | Pos v -> Bv_eq v
  | Neg v -> Bv_neg v

let idef_of_rep = function
  | Pos v -> Iv_eq v
  | Neg v -> Iv_opp v

let rec brepr st v =
  match st.bdefs.(v) with
  | Bv_eq p ->
    let d = brepr st p in
    (st.bdefs.(v) <- bdef_of_rep d ; d)
  | Bv_neg p ->
    let d = neg_rep (brepr st p) in
    (st.bdefs.(v) <- bdef_of_rep d ; d)
  | _ -> Pos v
and irepr st v =
  match st.idefs.(v) with
  | Iv_eq p ->
    let d = irepr st p in
    (st.idefs.(v) <- idef_of_rep d ; d)
  | Iv_opp p ->
    let d = neg_rep (irepr st p) in
    (st.idefs.(v) <- idef_of_rep d ; d)
  | _ -> Pos v

let to_ivars xs = Pr.Arr (Array.map (fun y -> Pr.Ivar y) xs)

let fzn_assert_eq st x def = failwith "Implement"
(*
let fzn_assert_eq st x def =
  Dy.add st.cons
    match def with
    | Def_none -> failwith "fzn_assert_eq called with Def_none"
    | Def_blit b -> (("bool_eq", [|x ; Pr.Blit b|]), [])
    | Def_ilit k -> (("int_eq", [|x ; Pr.Ilit k|]), [])
    (* Aliasing *)
    | Def_eq y -> failwith "Fixme: need to know kind of x, y"
    (* Boolean functions *)
    | Def_bne y -> (("bool_ne", [|x ; Pr.Bvar y|]), [])
    | Def_at (y, r, k) ->
      fzn_irel_reif r (Pr.Bvar x) (Pr.Ivar y) (Pr.Ilit k)
    | Def_or ys ->
      (("array_bool_or", [| to_ivars ys ; x |]), [])
    | Def_and ys -> 
      (("array_bool_and", [| to_ivars ys ; x |]), [])
    (* Arithmetic functions *)
    | Def_sum ys -> 
      (( 
    | Def_prod of val_id array
    | Def_max of val_id array
    | Def_min of val_id array
    | Def_b2i of val_id
    *)
  
(* Precondition - v and v' are class reprs. *)
(*
let merge_reprs st invert v v' =
  if v <> v' then
    (* Need to handle reordering at instantiation *)
    let w, w' = v, v' in
    (* let w, w' = min v v', max v v' in *)
    match st.defs.(w), st.defs.(w') with
    | (dw, Def_none
      | Def_none, dw) ->
      begin
        st.defs.(w) <- dw ;
        st.defs.(w') <- (if invert then Def_bne w else Def_eq w)
      end
    | Some (At _), Some (At (x, r, k)) ->
      begin
        if invert then
          (st.defs.(w') <- Some (Bneg w) ;
           Dy.add st.cons
             (fzn_irel_reif (irel_neg r) (Pr.Bvar w) (Pr.Ivar x) (Pr.Ilit k)))
        else
          (st.defs.(w') <- Some (Beq w) ;
           Dy.add st.cons
             (fzn_irel_reif r (Pr.Bvar w) (Pr.Ivar x) (Pr.Ilit k)))
      end
    | _, _ -> failwith "merge_reprs should only be called with representatives."
  else
    if invert then failwith "Top level inconsistency: b = ~b."

let merge_r st invert v w =
  match repr st w with
  | Pos w' -> merge_reprs st invert v w'
  | Neg w' -> merge_reprs st (not invert) v w'

let merge st invert v w =
  match repr st v with
  | Pos v' -> merge_r st invert v' w
  | Neg v' -> merge_r st (not invert) v' w

let apply_def st v (def : bdef) =
  (* Find the representative *)
  let v', def' =
    match repr st v with
    | Pos v' -> v', def
    | Neg v' -> v', bdef_neg def in
  match st.defs.(v') with
  | None -> st.defs.(v') <- Some def'
  | Some _ ->
    begin
      match def' with
      | Beq w -> merge_r st false v' w
      | Bneg w -> merge_r st true v' w
      | At (x, rel, k) -> 
        Dy.add st.cons (fzn_irel_reif rel (Pr.Bvar v') (Pr.Ivar x) (Pr.Ilit k))
    end
 *)
let bmerge st invert x y = failwith "Implement"
let imerge st invert x y = failwith "Implement"

let apply_bdef st v def = failwith "Implement"
let apply_idef st v def = failwith "Implement"

let set_bool st x b = apply_bdef st x (Bv_const b)
  (* Dy.add st.cons (("bool_eq", [| Pr.Bvar x; Pr.Blit b |]), []) *)
let set_int st x k = apply_idef st x (Iv_const k)
 
let simp_irel_reif rel st args anns =
  let r = Pr.get_bval args.(2) in
  match r with
  | Pr.Bv_bool true ->
    Dy.add st.cons (fzn_irel rel args.(0) args.(1))
  | Pr.Bv_bool false ->
    Dy.add st.cons (fzn_irel (irel_neg rel) args.(0) args.(1))
  | Pr.Bv_var b ->
    let x = Pr.get_ival args.(0) in
    let y = Pr.get_ival args.(1) in
    begin
      match x, y with
      | Pr.Iv_int a, Pr.Iv_int b ->
        let res = match rel with
          | Ile ->
            (Format.fprintf Format.err_formatter "{r} <-> %d <= %d@." a b ;
            a <= b)
          | Ieq -> a = b
          | Igt -> a > b
          | Ine -> a <> b in
        set_bool st b res
      | Pr.Iv_var x, Pr.Iv_int k ->
        apply_bdef st b (At (x, rel, k))
      | Pr.Iv_int k, Pr.Iv_var x ->
        let def = match rel with
          | Ile -> At (x, Igt, k-1)
          | Ieq -> At (x, Ieq, k)
          | Igt -> At (x, Ile, k-1)
          | Ine -> At (x, Ine, k)
        in
        apply_bdef st b def
      | Pr.Iv_var x, Pr.Iv_var y ->
        Dy.add st.cons (fzn_irel_reif rel (Pr.Bvar b) (Pr.Ivar x) (Pr.Ivar y))
      (* | _, _ -> Dy.add st.cons (fzn_irel_reif rel (Pr.Bvar b) args.(0) args.(1)) *)
    end

let simp_bool_eq st args anns =
  match Pr.get_bval args.(0), Pr.get_bval args.(1) with
  | Pr.Bv_bool x, Pr.Bv_bool y -> if x <> y then failwith "Found toplevel conflict in bool_eq" 
  | (Pr.Bv_bool b, Pr.Bv_var x
  |  Pr.Bv_var x, Pr.Bv_bool b) ->
    Dy.add st.cons (("bool_eq", [|Pr.Bvar x ; Pr.Blit b|]), anns)
  | Pr.Bv_var x, Pr.Bv_var y -> bmerge st false x y 
  (*
  | Pr.Bv_var x, Pr.Bv_var y -> 
    Dy.add st.cons (("bool_eq", [|Pr.Bvar x; Pr.Bvar y|]), anns)
    *)

 let simp_bool_ne st args anns =
  match Pr.get_bval args.(0), Pr.get_bval args.(1) with
  | Pr.Bv_bool x, Pr.Bv_bool y -> if x = y then failwith "Found toplevel conflict in bool_ne" 
  | (Pr.Bv_bool b, Pr.Bv_var x
  |  Pr.Bv_var x, Pr.Bv_bool b) ->
    Dy.add st.cons (("bool_ne", [|Pr.Bvar x ; Pr.Blit (not b)|]), anns)
  | Pr.Bv_var x, Pr.Bv_var y -> bmerge st true x y

let simplify_constraint state id args anns =
  try
    let simplifier = H.find registry id in
    simplifier state args anns
  with Not_found -> Dy.add state.cons ((id, args), anns)

let log_reprs idefs bdefs =
  if !Opts.verbosity > 0 then
    (*
    Util.print_array ~post:"|]@." (fun fmt def ->
      match def with
      | None -> Format.fprintf fmt "_"
      | Some (Bv_eq b) -> Format.fprintf fmt "%d" b
      | Some (Bv_neg b) -> Format.fprintf fmt "~%d" b
      | Some (At (x, r, k)) -> Format.fprintf fmt "x%d %s %d" x (rel_str r) k
    ) Format.std_formatter defs
    *)
    ()
  else ()

let simplify problem =
(*
  let bdefs = Array.make (Dy.length problem.Pr.bvals) None in
  (bdefs, problem)
  *)
  let state = init_state problem in
  Dy.iter
    (fun ((id, args), anns) -> simplify_constraint state id args anns)
    problem.Pr.constraints ;
  log_reprs state.idefs state.bdefs ;
  (state.idefs, state.bdefs, { problem with Pr.constraints = state.cons })

(* Register all the simplifiers. *)
let init () = 
  let handlers =
    [
      "int_le_reif", simp_irel_reif Ile ; 
      "int_eq_reif", simp_irel_reif Ieq ;
      "int_ne_reif", simp_irel_reif Ine ;
      "bool_eq", simp_bool_eq ; 
      "bool_ne", simp_bool_ne
    ] in
  List.iter (fun (id, h) -> H.add registry id h) handlers

let _ = init ()
