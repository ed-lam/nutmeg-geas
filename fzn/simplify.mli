(** Problem simplification *)
(*
type rel = Le | Eq | Gt | Ne
type bdef = bvar_id * rel * int

type ival_info = { id : ident ; dom : Dom.t ; ann : ann_expr list }
type model = {
  symbols : (ident, fzn_expr * ann_expr list) Hashtbl.t ;
  ivals : ival_info DynArray.t ;
  bvals : (ident * ann_expr list) DynArray.t ;
  constraints : (cstr * ann_expr list) DynArray.t ;
  mutable objective : (goal * ann_expr list)
}
*)

val simplify : Problem.t -> Problem.t
