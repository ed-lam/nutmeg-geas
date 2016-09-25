(* Constraint registry *)
type poster = (Solver.t -> (Fzn_model.expr array) -> bool)

exception Unknown_constraint of string

val register : string -> poster -> unit
val post : Solver.t -> string -> (Fzn_model.expr array) -> bool
