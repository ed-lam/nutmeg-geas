(* Interface file for a Flatzinc problem *)
(* FIXME: Deal with annotations *)

exception Sym_error of string
exception Type_mismatch

(* Constraint items *)
type ident = string
(*
type item = ident * (fzn_expr array) 
*)

type ival_id = int
type bval_id = int

(* Just model representation -- not worrying about
 * aliasing/definitions *)
type lbool = LFalse | LUndef | LTrue

type expr =
  | Ilit of int
  | Ivar of ival_id
  | Blit of bool
  | Bvar of bval_id
  | Arr of expr array
  (* | Call of ident * (expr list) *)

val get_int : expr -> int
val get_bool : expr -> bool
val get_ivar : expr -> ival_id
val get_bvar : expr -> bval_id
val get_array : (expr -> 'a) -> expr -> 'a array

type ann_expr =
  | Ann_int of int
  | Ann_bool of bool
  | Ann_str of string
  | Ann_set of Dom.t
  | Ann_id of ident
  | Ann_arr of ann_expr array
  | Ann_call of ident * (ann_expr array)

type goal =
  | Satisfy
  | Maximize of ival_id
  | Minimize of ival_id

type model = {
  symbols : (ident, expr) Hashtbl.t ;
  ivals : Dom.t DynArray.t ;
  bvals : lbool DynArray.t ;
  constraints : (ident * (expr array)) DynArray.t ;
  mutable objective : goal
}

type t = model

val create : unit -> t
val new_ival : t -> Dom.t -> ival_id
val new_bval : t -> bval_id

(* Bind an identifier to an expression *)
val bind : t -> ident -> expr -> unit
(* Resolve a variable to an expression *)
val resolve : t -> ident -> expr

(* Post a constraint *)
val post : t -> ident -> expr array -> expr array -> unit
