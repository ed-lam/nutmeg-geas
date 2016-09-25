(* Representation of domains for preprocessing *)
type ranges = (int * int) list

type t = ranges option

val range : int -> int -> t
val set : int list -> t
val free : t

val intersect : t -> t -> t

val iter : (int -> unit) -> t -> unit
