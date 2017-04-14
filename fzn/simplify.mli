(** Problem simplification *)
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

val simplify : Problem.t -> t
