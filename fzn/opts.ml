let infile = ref None
let outfile = ref None
let verbosity = ref 0

let print_stats = ref false
let quiet = ref false

let max_solutions = ref 1

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
       "-nof_solutions",
       Arg.Int (fun k -> max_solutions := k),
       " : maximum number of solutions to report"
     )
    ]
