(** Problem simplification *)
type val_id = int

type kind = 
  | Bool
  | Int of Dom.t
type irel = Ile | Ieq | Igt | Ine

type def = 
  | Def_none
  | Def_blit of bool
  | Def_ilit of int
  (* Aliasing *)
  | Def_eq of val_id
  (* Boolean functions *)
  | Def_bneg of val_id
  | Def_at of val_id * irel * int
  | Def_or of val_id array
  | Def_and of val_id array
  (* Arithmetic functions *)
  | Def_sum of val_id array
  | Def_prod of val_id array
  | Def_max of val_id array
  | Def_min of val_id array
  | Def_b2i of val_id
(*
type bdef =
  | Bv_const of bool
  | Bv_eq of Problem.bval_id
  | Bv_neg of Problem.bval_id
  | At of Problem.ival_id * irel * int

type idef = 
  | Iv_const of int
  | Iv_eq of Problem.ival_id
  | Iv_neg of Problem.ival_id
  | Bool2int of Problem.bval_id
  | Max of Problem.ival_id array
  | Min of Problem.ival_id array
  | Linex of (int * Problem.ival_id) array

type def =
  | Bvar of bdef option
  | Ivar of idef option
*)
type t = ((kind * def) array * Problem.t)

val simplify : Problem.t -> t
