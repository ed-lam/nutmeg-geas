(* Implementation of fast-ish congruence closure
 * Described in Nieuwenhuis & Oliveras, 2007. *)
type const_id = int

type ('v, 'f) const =
  | Var of 'v
  | Ftor of 'f
  
type ('v, 'f) t

val create : unit -> ('v, 'f) t

val add_var : ('v, 'f) t -> 'v -> const_id
val add_fun : ('v, 'f) t -> 'f -> const_id array -> const_id
val merge : ('v, 'f) t -> const_id -> const_id -> unit

(* How then do we inspect the result? *)
