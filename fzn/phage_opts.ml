let infile = ref None
let verbosity = ref 0

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
    ]
