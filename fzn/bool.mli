(* Boolean constraints, half-reified *)

val bool_or : Solver.t -> ?r:Atom.t -> Atom.t array -> bool
val bool_and : Solver.t -> ?r:Atom.t -> Atom.t array -> bool

val bool_iff : Solver.t -> ?r:Atom.t -> Atom.t -> Atom.t -> bool
val bool_xor : Solver.t -> ?r:Atom.t -> Atom.t -> Atom.t -> bool

val bool_linear_int : Solver.t -> ?r:Atom.t ->
  (int * Atom.t) array -> Arith.rel -> int -> bool
val bool_linear_var : Solver.t -> ?r:Atom.t ->
  (int * Atom.t) array -> Arith.rel -> int -> bool
