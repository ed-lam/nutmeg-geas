type env = {
  solver : Solver.t ;
  ivars : Solver.intvar array ;
  bvars : Atom.t array
}
type expr = Fzn_model.expr

type t = env

(* Extracting data from fzn_exprs *)
val expr_array : (t -> expr -> 'a) -> t -> expr -> 'a array
val expr_ivar : t -> expr -> Solver.intvar
val expr_bvar : t -> expr -> Atom.t

val create : Solver.t -> Fzn_model.t -> t
