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
let negate_rel = function
  | Ile -> Igt
  | Igt -> Ile
  | Ieq -> Ine
  | Ine -> Ieq

type ('b, 'i) idef = 
  | Iv_none
  | Iv_const of int
  (* Aliasing *)
  | Iv_eq of 'i
  | Iv_opp of 'i
  (* Arithmetic functions *)
  (* Maybe make this linear, rather than sum. *)
  | Iv_lin of (int * 'i) array
  | Iv_prod of 'i array
  | Iv_max of 'i array
  | Iv_min of 'i array
  | Iv_b2i of 'b

let negate_idef = function
  | Iv_const k -> Some (Iv_const (-k))
  | Iv_eq x -> Some (Iv_opp x)
  | Iv_opp x -> Some (Iv_eq x)
  | Iv_lin ts -> Some (Iv_lin (Array.map (fun (k, x) -> (-k, x)) ts))
  | _ -> None


type ('b, 'i) bdef =
  | Bv_none
  | Bv_const of bool
  | Bv_eq of 'b
  | Bv_neg of 'b
  | At of 'i * irel * int
  | Bv_or of 'b array
  | Bv_and of 'b array

type bdefn = (bval_id, ival_id) bdef
type idefn = (bval_id, ival_id) idef

let negate_bdef = function
  | Bv_const b -> Some (Bv_const (not b))
  | Bv_eq x -> Some (Bv_neg x)
  | Bv_neg x -> Some (Bv_eq x)
  | At (x, r, k) -> Some (At (x, negate_rel r, k))
  | _ -> None

let apply_snd f (a, b) = (a, f b)

let map_idef fb fi def =
  match def with
  | Iv_none -> Iv_none
  | Iv_const k -> Iv_const k
  | Iv_eq x -> Iv_eq (fi x)
  | Iv_opp x -> Iv_opp (fi x)
  | Iv_lin ts -> Iv_lin (Array.map (apply_snd fi) ts)
  | Iv_prod xs -> Iv_prod (Array.map fi xs)
  | Iv_max xs -> Iv_max (Array.map fi xs)
  | Iv_min xs -> Iv_min (Array.map fi xs)
  | Iv_b2i b -> Iv_b2i (fb b)

let map_bdef fb fi def =
  match def with
  | Bv_none -> Bv_none
  | Bv_const b -> Bv_const b
  | Bv_eq b -> Bv_eq (fb b)
  | Bv_neg b -> Bv_neg (fb b)
  | At (x, r, k) -> At (fi x, r, k)
  | Bv_or xs -> Bv_or (Array.map fb xs)
  | Bv_and xs -> Bv_and (Array.map fb xs)

type t = ((idefn array) * (bdefn array) * Problem.t)

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
  
type state = {
  idefs : idefn array ;
  bdefs : bdefn array ;
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

let to_bvars xs = Pr.Arr (Array.map (fun y -> Pr.Bvar y) xs)
let to_ivars xs = Pr.Arr (Array.map (fun y -> Pr.Ivar y) xs)

let fzn_assert_beq st x def =
  Dy.add st.cons
    begin match def with
      | Bv_none
      | Bv_const _
      | Bv_eq _ | Bv_neg _ -> failwith "fzn_assert_beq called on alias."
      | At (y, r, k) ->
        fzn_irel_reif r (Pr.Bvar x) (Pr.Ivar y) (Pr.Ilit k)
      | Bv_or ys -> (("array_bool_or", [| to_ivars ys ; Pr.Bvar x |]), [])
      | Bv_and ys -> (("array_bool_and", [| to_ivars ys ; Pr.Bvar x |]), [])
    end

let fzn_assert_ieq st x def =
  Dy.add st.cons
  begin match def with
  | Iv_none
  | Iv_const _ 
  | Iv_eq _
  | Iv_opp _ -> failwith "fzn_assert_ieq called on alias."
  (* Arithmetic functions *)
  | Iv_lin ts -> failwith "FIXME"
  | Iv_prod xs -> failwith "FIXME"
  | Iv_max xs -> (("array_int_maximum", [| Pr.Ivar x; to_ivars xs |]), [])
  | Iv_min xs -> (("array_int_minimum", [| Pr.Ivar x; to_ivars xs |]), [])
  | Iv_b2i b -> (("bool2int", [| Pr.Bvar b; Pr.Ivar x |]), [])
  end
 
(* Precondition - v and v' are class reprs. *)
let beq_def st invert x = if invert then Bv_neg x else Bv_eq x

let evict_bdef st invert x y =
  let ry = st.bdefs.(y) in 
  (st.bdefs.(y) <- beq_def st invert x ;
   fzn_assert_beq st y ry)

(*
let rec bmerge st invert x y =
  match st.bdefs.(x), st.bdefs.(y) with
  | Bv_none, dy -> st.bdefs.(x) <- beq_def st invert y
  | dx, Bv_none -> st.bdefs.(y) <- beq_def st invert x
  | Bv_eq rx, _ -> bmerge st invert rx y
  | _, Bv_eq ry -> bmerge st invert x ry
  | Bv_neg rx, _ -> bmerge st (not invert) rx y
  | _, Bv_neg ry -> bmerge st (not invert) x ry
  (* Otherwise, we need to choose one of the definitions to evict. *)
  | Bv_const a, Bv_const b ->
    if a <> b then
      (* Conflicting definition *)
      failwith "Top-level failure."
    else ()
  (* If one is a const, keep that. *)
  | Bv_const a, ry ->
    (st.bdefs.(y) <- Bv_const (a <> invert) ;
     fzn_assert_beq st y ry)
  | rx, Bv_const b ->
    (st.bdefs.(x) <- Bv_const (b <> invert) ;
     fzn_assert_beq st x rx)
  (* Or an atom *)
  | At _, _ -> evict_bdef st invert x y
  | _, At _ -> evict_bdef st invert y x
  | _, _ -> evict_bdef st invert x y
  *)

let rec resolve_bdefs st v d d' = 
  match d, d' with
  (* No conflict *)
  | Bv_none, def
  | def, Bv_none -> st.bdefs.(v) <- def
  (* Aliasing *)
  | Bv_eq v', def
  | def, Bv_eq v' ->
    if v = v' then
      st.bdefs.(v) <- def
    else
      (st.bdefs.(v) <- Bv_eq v' ;
       resolve_bdefs st v st.bdefs.(v') def)
  | Bv_neg v', def
  | def, Bv_neg v' -> 
    if v = v' then 
      failwith "Top-level failure: x = ~x (var)."
    else
      begin match negate_bdef def with
        | Some def' ->
          (st.bdefs.(v) <- Bv_neg v' ;
           resolve_bdefs st v st.bdefs.(v') def')
        | None -> fzn_assert_beq st v def
      end
  (* First priority to constants *)
  | Bv_const b, Bv_const b' ->
    if b <> b' then
      failwith "Top-level failure: x = ~x (const)"
    else
      st.bdefs.(v) <- Bv_const b
  | ((Bv_const _) as d1), d2 
  | d2, ((Bv_const _) as d1)
  (* Then atoms *)
  | ((At _) as d1), d2
  | d2, ((At _) as d1)
  (* Then whatever *)
  | d1, d2 ->
    (st.bdefs.(v) <- d1 ; fzn_assert_beq st v d2)

let rec resolve_idefs st v d d' =
  match d, d' with
  (* No conflict *)
  | Iv_none, def
  | def, Iv_none -> st.idefs.(v) <- def
  (* Aliasing *)
  | Iv_eq v', def
  | def, Iv_eq v' ->
    if v = v' then
      st.idefs.(v) <- def
    else
      (st.idefs.(v) <- Iv_eq v' ;
       resolve_idefs st v st.idefs.(v') def)
  | Iv_opp v', def
  | def, Iv_opp v' -> 
    if v = v' then 
      failwith "Top-level failure: x = ~x."
    else
      begin match negate_idef def with
        | Some def' ->
          (st.idefs.(v) <- Iv_opp v' ;
           resolve_idefs st v st.idefs.(v') def')
        | None -> fzn_assert_ieq st v def
      end
  | d1, d2 ->
    (st.idefs.(v) <- d1; fzn_assert_ieq st v d2)
    (* FIXME: Add special cases *)
  (*
  (* Arithmetic functions *)
  | Iv_lin xs -> failwith "FIXME"
  | Iv_prod xs -> failwith "FIXME"
  | Iv_max xs -> (("array_int_maximum", [| Pr.Ivar x; to_ivars xs |]), [])
  | Iv_min xs -> (("array_int_minimum", [| Pr.Ivar x; to_ivars xs |]), [])
  | Iv_b2i b -> (("bool2int", [| Pr.Bvar b; Pr.Ivar x |]), [])
  *)

let set_bool st x b = resolve_bdefs st x st.bdefs.(x) (Bv_const b)
  (* Dy.add st.cons (("bool_eq", [| Pr.Bvar x; Pr.Blit b |]), []) *)
let set_int st x k = resolve_idefs st x st.idefs.(x) (Iv_const k)

let apply_bdef st x d = resolve_bdefs st x st.bdefs.(x) d
let apply_idef st x d = resolve_idefs st x st.idefs.(x) d
 
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
      | Pr.Iv_int u, Pr.Iv_int v ->
        let res = match rel with
          | Ile ->
            ( (*Format.fprintf Format.err_formatter "{r} <-> %d <= %d@." u v ; *)
            u <= v)
          | Ieq -> u = v
          | Igt -> u > v
          | Ine -> u <> v in
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
  | Pr.Bv_var x, Pr.Bv_var y -> apply_bdef st x (Bv_eq y)
  (*
  | Pr.Bv_var x, Pr.Bv_var y -> 
    Dy.add st.cons (("bool_eq", [|Pr.Bvar x; Pr.Bvar y|]), anns)
    *)

 let simp_bool_ne st args anns =
  match Pr.get_bval args.(0), Pr.get_bval args.(1) with
  | Pr.Bv_bool x, Pr.Bv_bool y -> if x = y then failwith "Found toplevel conflict in bool_ne" 
  | (Pr.Bv_bool b, Pr.Bv_var x
  |  Pr.Bv_var x, Pr.Bv_bool b) ->
    (* Dy.add st.cons (("bool_ne", [|Pr.Bvar x ; Pr.Blit (not b)|]), anns) *)
    apply_bdef st x (Bv_const b)
  | Pr.Bv_var x, Pr.Bv_var y -> apply_bdef st x (Bv_eq y)

let simp_int_eq st args anns =
  match Pr.get_ival args.(0), Pr.get_ival args.(1) with
  | (Pr.Iv_int x, Pr.Iv_int y) -> if x <> y then failwith "Found toplevel conflict in int_eq."
  | ( Pr.Iv_var x, Pr.Iv_int k
    | Pr.Iv_int k, Pr.Iv_var x) ->
      apply_idef st x (Iv_const k)
  | (Pr.Iv_var x, Pr.Iv_var y) -> apply_idef st x (Iv_eq y)

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
      "int_eq", simp_int_eq ;
      "bool_eq", simp_bool_eq ; 
      "bool_ne", simp_bool_ne
    ] in
  List.iter (fun (id, h) -> H.add registry id h) handlers

let _ = init ()
