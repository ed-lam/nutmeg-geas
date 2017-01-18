(** Problem simplification *)
module H = Hashtbl
module Dy = DynArray

module Pr = Problem

type irel = Ile | Ieq | Igt | Ine
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
  
type bdef =
  | Beq of Problem.bval_id
  | Bneg of Problem.bval_id
  | At of Problem.ival_id * irel * int

let bdef_neg = function
  | Beq p -> Bneg p
  | Bneg p -> Beq p
  | At (x, r, k) -> At (x, irel_neg r, k)

(* Currently a no-op *)
type state = {
  defs : bdef option array ;
  cons : (Pr.cstr * Pr.ann_expr list) Dy.t
}

let registry = H.create 17

let init_state pr =
  { defs = Array.make (Dy.length pr.Pr.bvals) None ;
    cons = Dy.create () }

let set_bool st x b =
  (* FIXME: Add new definition *)
  if b then
    Dy.add st.cons (("bool_clause", [| Pr.Arr [|Pr.Bvar x|]; Pr.Arr [| |] |]), [])
  else
    Dy.add st.cons (("bool_clause", [| Pr.Arr [| |]; Pr.Arr [|Pr.Bvar x|] |]), [])
 
(* Dealing with signed union-find stuff *)
type rep = Pos of int | Neg of int
let neg_rep = function
  | Pos v -> Neg v
  | Neg v -> Pos v
let def_of_rep = function
  | Pos v -> Some (Beq v)
  | Neg v -> Some (Bneg v)

let rec repr st v =
  match st.defs.(v) with
  | Some (Beq p) ->
    let d = repr st p in
    (st.defs.(v) <- def_of_rep d ; d)
  | Some (Bneg p) ->
    let d = neg_rep (repr st p) in
    (st.defs.(v) <- def_of_rep d ; d)
  | _ -> Pos v
    
(* Precondition - v and v' are class reprs. *)
let merge_reprs st invert v v' =
  if v <> v' then
    let w, w' = min v v', max v v' in
    match st.defs.(w), st.defs.(w') with
    | (dw, None
      | None, dw) ->
      begin
        st.defs.(w) <- dw ;
        st.defs.(w') <- Some (if invert then Bneg w else Beq w)
      end
      (*
        st.defs.(v') <- Some (if invert then Bneg v else Beq v)
        *)
      (*
    | None, dw -> st.defs.(v) <- Some (if invert then Bneg v' else Beq v')
    *)
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
          | Ile -> a <= b
          | Ieq -> a = b
          | Igt -> a > b
          | Ine -> a <> b in
        set_bool st b res
      | Pr.Iv_var x, Pr.Iv_int k ->
        apply_def st b (At (x, rel, k))
      | Pr.Iv_int k, Pr.Iv_var x ->
        let def = match rel with
          | Ile -> At (x, Igt, k-1)
          | Ieq -> At (x, Ieq, k)
          | Igt -> At (x, Ile, k-1)
          | Ine -> At (x, Ine, k)
        in
        apply_def st b def
      | Pr.Iv_var x, Pr.Iv_var y ->
        Dy.add st.cons (fzn_irel_reif rel (Pr.Bvar b) (Pr.Ivar x) (Pr.Ivar y))
    end

let simp_bool_eq st args anns =
  match Pr.get_bval args.(0), Pr.get_bval args.(1) with
  | Pr.Bv_bool x, Pr.Bv_bool y -> if x <> y then failwith "Found toplevel conflict in bool_eq" 
  | (Pr.Bv_bool b, Pr.Bv_var x
  |  Pr.Bv_var x, Pr.Bv_bool b) ->
    Dy.add st.cons (("bool_eq", [|Pr.Bvar x ; Pr.Blit b|]), anns)
  | Pr.Bv_var x, Pr.Bv_var y -> merge st false x y 
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
  | Pr.Bv_var x, Pr.Bv_var y -> merge st true x y

let simplify_constraint state id args anns =
  try
    let simplifier = H.find registry id in
    simplifier state args anns
  with Not_found -> Dy.add state.cons ((id, args), anns)

let log_reprs defs =
  Util.print_array ~post:"|]@." (fun fmt def ->
    match def with
    | None -> Format.fprintf fmt "_"
    | Some (Beq b) -> Format.fprintf fmt "%d" b
    | Some (Bneg b) -> Format.fprintf fmt "~%d" b
    | Some (At (x, r, k)) -> Format.fprintf fmt "x%d %s %d" x (rel_str r) k
  ) Format.std_formatter defs

let simplify problem =
  (*
  let bdefs = Array.make (Dy.length problem.Pr.bvals) None in
  (bdefs, problem)
  *)
  let state = init_state problem in
  Dy.iter
    (fun ((id, args), anns) -> simplify_constraint state id args anns)
    problem.Pr.constraints ;
  log_reprs state.defs ;
  (state.defs, { problem with Pr.constraints = state.cons })

(* Register all the simplifiers. *)
let init () = 
  let handlers =
    [
      "int_le_reif", simp_irel_reif Ile ;
      (*
      "int_eq_reif", simp_irel_reif Ieq ;
      "int_ne_reif", simp_irel_reif Ine ;
      *)
      (*
      "bool_eq", simp_bool_eq ; 
      "bool_ne", simp_bool_ne
      *)
    ] in
  List.iter (fun (id, h) -> H.add registry id h) handlers

let _ = init ()
(*

(* Simplifier definitions *)
let array_bool_and solver args anns =
  let xs = Pr.get_array get_atom args.(0) in
  let z = get_atom args.(1) in
  Array.fold_left
    (fun b x -> b && S.post_clause solver [|At.neg z; x|])
    (S.post_clause solver
                   (Array.append [|z|] (Array.map At.neg xs))) xs

*)

(*
let simp_le pr terms k =
  let all_bool = ref true in
  let terms', k' = Array.fold_left (fun (acc, k') (c, x) ->
    match c, x with
    | Ilit c, Ilit x -> acc, k - (c*x)
    | Ilit c, Ivar v ->
      let d = Pr.dom_of pr x in
      begin
      match Dom.size d with
      | 1 -> acc, k - (c * (Dom.lb d))
      | 2 -> ((Pr.Ilit c, Pr.Ivar v) :: acc), k'
      | _ -> (all_bool := false ; ((Ilit c, Ivar v) :: acc))
      if dom_size d = 1 then
        acc, k - (c * (Dom.lb pr x))
      else
        ((Ilit c, Ivar v) :: acc), k'
    | _ -> failwith "Expected ilit or ivar") ([], k) terms in
  List.rev terms', k'
  *)

(*
let int_lin_le args anns =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array  args.(1) in
  let terms = Array.init (Array.length xs)
                         (fun i -> cs.(i) , xs.(i)) in
  let k = Pr.get_int args.(2) in
  match simp_le terms k with
  | [(1, x) ; (-1, y)], k' -> [("int_diff", [|x; y; Pr.Ilit k'|]), anns]
  | [(-1, y) ; (1, x)], k' -> [("int_diff", [|x; y; Pr.Ilit k'|]), anns]
  | terms', k' ->
    let tarr = Array.of_list terms' in
    [("int_lin_le", Pr.Arr (Array.map fst terms'), Pr.Arr (Array.map snd terms')]
  ("int_lin_le", args), anns
  *)
