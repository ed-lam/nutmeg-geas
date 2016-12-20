(* Representation of domains for preprocessing *)
type t =
  | Range of int * int
  | Set of int list

val range : int -> int -> t
val set : int list -> t

val union : t -> t -> t

val bounds : t -> (int * int)
val holes : t -> (int * int) list
