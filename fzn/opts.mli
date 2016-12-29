val infile : string option ref
val outfile : string option ref

val verbosity : int ref

val quiet : bool ref

val max_solutions : int ref
val print_stats : bool ref

val native : bool ref

(* --------------------------------------------- *)
(*       Specification list for options          *)
(* --------------------------------------------- *)
val speclist : (Arg.key * Arg.spec * Arg.doc) list ;;
