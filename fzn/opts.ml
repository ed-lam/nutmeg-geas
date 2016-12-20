let infile = ref None
let outfile = ref None
let verbosity = ref 0

let noop = ref false
let quiet = ref false

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
       "-noop",
       Arg.Unit (fun () -> noop := true),
       " : skip processing the model"
     ) ;
     (
       "-native",
       Arg.Unit (fun () -> native := true),
       " : rewrite only into 'standard' constraints (so no _HR variants)"
     )
    ]
