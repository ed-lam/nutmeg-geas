(* Constraint registry *)
type poster = (Fzn_env.t -> (Fzn_model.expr array) -> bool)

exception Unknown_constraint of string

val register : string -> poster -> unit
val post : Fzn_env.t -> string -> (Fzn_model.expr array) -> bool
