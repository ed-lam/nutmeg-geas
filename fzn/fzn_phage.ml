module S = Stream
module Dy = DynArray

open Fzn_token
module P = Fzn_parser
module Opt = Phage_opts
module M = Fzn_model

(*
let tok_str = function
  | Kwd k -> "{KWD}"
  | Id s -> s
  | Str s -> "\"" ^ s ^ "\""
  | Int i -> string_of_int i
  | Bool b -> if b then "true" else "false"
  *)

let main () =
  (* Parse the command-line arguments *)
  Arg.parse
    Phage_opts.speclist
      (begin fun infile -> Opt.infile := Some infile end)
      "fzn_phage <options> <inputfile>"
  ;
  (* Parse the program *)
  let input = match !Opt.infile with
      | None -> stdin
      | Some file -> open_in file
  in
  let lexer = P.lexer input in
  (* *)
  let model = P.read_model lexer in
  Format.printf
    "Info: %d intvars, %d boolvars, %d constraints@."
    (Dy.length model.M.ivals)
    (Dy.length model.M.bvals)
    (Dy.length model.M.constraints)
  (* *)
  (* )
  while S.peek lexer <> None
  do
    Format.printf "%s@." (tok_str (S.next lexer))
  done
  ( *)


let _ = main ()
