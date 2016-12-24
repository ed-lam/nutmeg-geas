(** Constraint registry *)
type expr = (Solver.intvar, Atom.t) Problem.expr

type poster = Solver.t -> expr array -> Problem.ann_expr list -> bool

val initialize : unit -> unit

val register : string -> poster -> unit
val lookup : string -> poster
