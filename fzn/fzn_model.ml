(* Interface file for a Flatzinc problem *)
(* FIXME: Deal with annotations *)
module Dy = DynArray
module H = Hashtbl

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

let get_int = function
  | Ilit k -> k
  | _ -> raise Type_mismatch

let get_bool = function
  | Blit b -> b
  | _ -> raise Type_mismatch

let get_ivar = function
  | Ivar v -> v
  | _ -> raise Type_mismatch

let get_bvar = function
  | Bvar v -> v
  | _ -> raise Type_mismatch

let get_array f = function
  | Arr x -> Array.map f x
  | _ -> raise Type_mismatch

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
  symbols : (ident, expr) H.t ;
  ivals : Dom.t Dy.t ;
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



