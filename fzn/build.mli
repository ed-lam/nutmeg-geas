(* Instantiate a problem in a solver, returning
 * a mapping from problem to solver variables. *)

type env = { ivars : Solver.intvar array ; bvars : Atom.atom array }

val build_problem : Solver.t -> Simplify.t -> Polarity.t -> env
