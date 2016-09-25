(* Arithmetic constraints, all half-reified *)
type rel = Le | Ge | Lt | Gt | Eq | Ne

(* r -> sum (c_i x_i) op k *)
val int_linear :
  Solver.t -> ?r:Atom.t -> (int * Solver.intvar) array -> rel -> int -> bool

val int_abs : Solver.t -> ?r:Atom.t ->
  Solver.intvar -> Solver.intvar -> bool
val int_mul : Solver.t -> ?r:Atom.t ->
  Solver.intvar -> Solver.intvar -> Solver.intvar -> bool
val int_div : Solver.t -> ?r:Atom.t ->
  Solver.intvar -> Solver.intvar -> Solver.intvar -> bool
val int_max : Solver.t -> ?r:Atom.t ->
  Solver.intvar -> Solver.intvar array -> bool
val int_min : Solver.t -> ?r:Atom.t ->
  Solver.intvar -> Solver.intvar array -> bool
