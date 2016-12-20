module S = Stream
module H = Hashtbl
module Dy = DynArray

module U = Util

open Token
module P = Parser

module Pr = Problem

module Sol = Solver

exception Unknown_constraint of string

let put = Format.fprintf

let make_intvar solver dom =
  let lb, ub = Dom.bounds dom in
  (* Create the var *)
  let v = Sol.new_intvar solver lb ub in
  (* Punch any holes. post_clause should never fail here. *)
  (* FIXME: export bindings for sparse vars. *)
  List.iter
    (fun (hl, hu) ->
     ignore @@
       Sol.post_clause solver
                       [|Sol.ivar_lt v hl ; Sol.ivar_gt v hu|]) (Dom.holes dom)  ;
  (* Then return the constructed variable *)
  v

(* Constraint registry. FIXME: Maybe move to a separate module. *)
let registry = H.create 17

type env = { ivars : Sol.intvar array ; bvars : Atom.atom array }

let rec resolve_expr env expr =
  match expr with
  | Pr.Ilit v -> Pr.Ilit v
  | Pr.Ivar iv -> Pr.Ivar env.ivars.(iv)
  | Pr.Blit b -> Pr.Blit b
  | Pr.Bvar bv -> Pr.Bvar env.bvars.(bv)
  | Pr.Set dom -> Pr.Set dom
  | Pr.Arr es -> Pr.Arr (Array.map (resolve_expr env) es)

let post_constraint solver env ident expr anns = 
  try
    let handler = H.find registry ident in
    handler solver (resolve_expr env) anns
  with Not_found ->
    (* raise (Unknown_constraint ident) *)
       Format.fprintf Format.err_formatter "Warning: Unknown constraint '%s'.@." ident

let build_problem solver problem =
  (* Allocate variables *)
  let ivars =
    Array.init
      (Dy.length problem.Pr.ivals)
      (fun i ->
       let vinfo = Dy.get problem.Pr.ivals i in
       make_intvar solver vinfo.Pr.dom)
  in
  let bvars =
    Array.init
      (Dy.length problem.Pr.bvals)
      (fun i -> Sol.new_boolvar solver)
  in
  let env = { ivars = ivars; bvars = bvars } in
  (* Process constraints *)
  Dy.iter (fun ((ident, expr), anns) ->
           post_constraint solver env ident expr anns)
          problem.Pr.constraints ;
  (* Then, return the bindings *)
  env

let solve_satisfy solver =
  let fmt = Format.std_formatter in
  match Sol.solve solver (-1) with
  | Sol.UNKNOWN -> Format.fprintf fmt "UNKNOWN@."
  | Sol.UNSAT -> Format.fprintf fmt "UNSAT@."
  | Sol.SAT -> Format.fprintf fmt "SAT@."

let decrease_ivar ivar solver model =
  let model_val = Sol.int_value model ivar in
  Sol.post_atom solver (Sol.ivar_lt ivar model_val)
      
let increase_ivar ivar solver model =
  let model_val = Sol.int_value model ivar in
  Sol.post_atom solver (Sol.ivar_gt ivar model_val)

let solve_optimize constrain solver =
  let fmt = Format.std_formatter in
  let rec aux model =
    if not (constrain solver model) then
      Format.fprintf fmt "OPTIMAL@."
    else
      match Sol.solve solver (-1) with
      | Sol.UNKNOWN -> Format.fprintf fmt "INCOMPLETE@."
      | Sol.UNSAT -> Format.fprintf fmt "OPTIMAL@."
      | Sol.SAT -> aux (Sol.get_model solver)
  in
  match Sol.solve solver (-1) with
  | Sol.UNKNOWN -> Format.fprintf fmt "UNKNOWN@."
  | Sol.UNSAT -> Format.fprintf fmt "UNSAT@."
  | Sol.SAT -> aux (Sol.get_model solver)
 
let main () =
  (* Parse the command-line arguments *)
  Arg.parse
    Opts.speclist
      (begin fun infile -> Opts.infile := Some infile end)
      "fzn_phage <options> <inputfile>"
  ;
  Half_reify.initialize () ;
  (* Parse the program *)
  let input = match !Opts.infile with
      | None -> stdin
      | Some file -> open_in file
  in
  let lexer = P.lexer input in
  let orig_problem = P.read_problem lexer in
  let problem = Simplify.simplify orig_problem in
  let solver = Sol.new_solver () in
  (* Do stuff *)
  let env = build_problem solver problem in
  (*
  let problem_HR =
    if !Opts.noop then
      problem
    else
      Half_reify.half_reify problem in
   *)
  (*
  if not !Opts.quiet then
    begin
      let output = match !Opts.outfile with
          | None -> stdout
          | Some file -> open_out file in 
      let fmt = Format.formatter_of_out_channel output in
      (* Pr.print fmt problem_HR ; *)
      Pr.print fmt problem ;
      close_out output
    end ;
   *)
  match fst problem.Pr.objective with
  | Pr.Satisfy -> solve_satisfy solver
  | Pr.Minimize obj ->
     solve_optimize (decrease_ivar env.ivars.(obj)) solver
  | Pr.Maximize obj ->
     solve_optimize (increase_ivar env.ivars.(obj)) solver

let _ = main ()
