(* Interface file for a Flatzinc problem *)
(* FIXME: Deal with annotations *)
module Dy = DynArray
module H = Hashtbl
module Dom = Fzn_dom

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
  eq_vals : (int, bval_id) H.t ;
  le_vals : (int, bval_id) H.t
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
  symbols : (ident, binding) H.t ;
  ivals : ival_def Dy.t ;
  bvals : bval_def Dy.t ;
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
  symbols : (ident, expr) H.t ;
  ivals : Fzn_dom.t Dy.t ;
  bvals : lbool Dy.t ;
  constraints : (ident * (expr array)) Dy.t ;
  mutable objective : goal
}

type t = model

let create () = {
  symbols = H.create 17 ;
  ivals = Dy.create () ;
  bvals = Dy.create () ;
  constraints = Dy.create () ;
  objective = Satisfy
}

let new_ival m dom =
  let id = Dy.length m.ivals in
  Dy.add m.ivals dom ;
  id

let new_bval m =
  let id = Dy.length m.bvals in
  Dy.add m.bvals LUndef ;
  id

let post model id args anns =
  Dy.add model.constraints (id, args)

let resolve m id =
  try
    H.find m.symbols id
  with Not_found -> raise (Sym_error id)

let bind m id expr =
  try
    let _ = H.find m.symbols id in
    failwith (Format.sprintf "Identifier %s already bound" id)
  with Not_found -> H.add m.symbols id expr
