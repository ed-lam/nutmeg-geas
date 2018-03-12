type stats_mode = 
  | Suppress
  | Compact
  | Verbose

val infile : string option ref
val outfile : string option ref

val verbosity : int ref

val quiet : bool ref

val max_solutions : int ref

val print_stats : stats_mode ref
val free : bool ref
val pol : bool ref
val half_reify : bool ref

val restart_limit : int option ref
(* val conflict_limit : int ref *)
val limits : Solver.limits ref

val check : bool ref

val native : bool ref

(* --------------------------------------------- *)
(*       Specification list for options          *)
(* --------------------------------------------- *)
val speclist : (Arg.key * Arg.spec * Arg.doc) list ;;
