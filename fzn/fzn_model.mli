(* Interface file for a Flatzinc problem *)
(* FIXME: Deal with annotations *)

exception Sym_error of string

(* Constraint items *)
type ident = string
(*
type item = ident * (fzn_expr array) 
*)

type ival_id = int
type bval_id = int

(*
type bval_def =
  | B_free
  | B_const of bool
  | B_alias of bval_id
  | B_neg of bval_id
  | B_eq of (ival_id * int)
  | B_le of (ival_id * int)

type ival_def =
  | I_alias of ival_id
  | I_dom of Fzn_dom.t
  | I_bool2int of bval_id

type ival_info = {
  mutable idef : ival_def ;
  eq_vals : (int, bval_id) Hashtbl.t ;
  le_vals : (int, bval_id) Hashtbl.t
}

type bval_info = {
  mutable bdef : bval_def ;
  mutable iview : ival_ref option;
  mutable neg : bval_ref option
}
*)

(*
type binding =
  | Ival of ival_id
  | Bval of bval_id
  | Aval of binding array
  
type model = {
  symbols : (ident, binding) Hashtbl.t ;
  ivals : ival_def DynArray.t ;
  bvals : bval_def DynArray.t ;
  items : item array
}
*)

(* Just model representation -- not worrying about
 * aliasing/definitions *)
type lbool = LFalse | LUndef | LTrue

type expr =
  | Ilit of int
  | Ivar of ival_id
  | Blit of bool
  | Bvar of bval_id
  (* | Set of Fzn_dom.t *)
  | Arr of expr array
  (* | Call of ident * (expr list) *)

type ann_expr =
  | Ann_int of int
  | Ann_bool of bool
  | Ann_str of string
  | Ann_set of Fzn_dom.t
  | Ann_id of ident
  | Ann_arr of ann_expr array
  | Ann_call of ident * (ann_expr array)

type goal =
  | Satisfy
  | Maximize of ival_id
  | Minimize of ival_id

type model = {
  symbols : (ident, expr) Hashtbl.t ;
  ivals : Fzn_dom.t DynArray.t ;
  bvals : lbool DynArray.t ;
  constraints : (ident * (expr array)) DynArray.t ;
  mutable objective : goal
}

type t = model

val create : unit -> t
val new_ival : t -> Fzn_dom.t -> ival_id
val new_bval : t -> bval_id

(* Bind an identifier to an expression *)
val bind : t -> ident -> expr -> unit
(* Resolve a variable to an expression *)
val resolve : t -> ident -> expr

(* Post a constraint *)
val post : t -> ident -> expr array -> expr array -> unit

