let infile = ref None
let outfile = ref None
let verbosity = ref 0

let print_stats = ref false
let quiet = ref false

let max_solutions = ref 1
let free = ref false
let pol = ref true
let half_reify = ref false

let restart_limit = ref None
let conflict_limit = ref 0

let check = ref false

let native = ref false

(* --------------------------------------------- *)
(*       Specification list for options          *)
(* --------------------------------------------- *)
let (speclist:(Arg.key * Arg.spec * Arg.doc) list) =
  Arg.align
    [(
      "-verbosity",
      Arg.Set_int(verbosity),
      "<int> : verbosity level, from 0 to 2 (default:0)"
     ) ;
     (
      "-S",
      Arg.Unit (fun () -> print_stats := true),
      " : print statistics"
     ) ;
     (
      "-o",
      Arg.String (fun s -> outfile := Some s) ,
      "<string> : file to write transformed model"
     ) ;
     (
       "-q",
       Arg.Unit (fun () -> quiet := true),
       " : suppress printing of model"
     ) ;
     (
      "-check",
      Arg.Unit (fun () -> check := true),
      " : check solutions"
     ) ;
     (
      "-f",
      Arg.Unit (fun () -> free := true),
      " : free search"
     ) ;
     (
      "-pol",
      Arg.Bool (fun b -> pol := b),
      " : use polarity analysis"
     ) ;
     (
      "-half-reif",
      Arg.Bool (fun b -> half_reify := b),
      " : use polarity analysis"
     ) ;
     (
       "-nof_solutions",
       Arg.Int (fun k -> max_solutions := k),
       " : maximum number of solutions to report"
     ) ;
     (
      "-a",
      Arg.Unit (fun () -> max_solutions := 0),
      " : find all solutions"
     ) ;
     (
      "-r",
      Arg.Int (fun r -> restart_limit := Some r),
      "<int> : initial restart limit"
     ) ;
     (
      "-c",
      Arg.Int (fun c -> conflict_limit := c),
      "<int> : maximum number of conflicts"
     ) ;
    ]
