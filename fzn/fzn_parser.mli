(* Recursive-descent parser for FlatZinc. *)
exception Tok_error of Fzn_token.t

val lexer : in_channel -> Fzn_token.t Stream.t

(*
val read_item :
  (Lexing.lexbuf -> Fzn_token.t) -> Fzn_model.t ->
  Lexing.lexbuf -> unit
  *)

val read_item : Fzn_model.t -> Fzn_token.t Stream.t -> unit

val read_model : Fzn_token.t Stream.t -> Fzn_model.t
