(** Replace full- with half-reification where possible *)

(** Initialize rewriting rules *)
val initialize : unit -> unit

(** Rewrite a problem *)
val half_reify : Problem.t -> Problem.t
