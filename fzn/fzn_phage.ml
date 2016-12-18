module S = Stream
module Dy = DynArray

module Opt = Phage_opts

open Fzn_token
module P = Fzn_parser
module M = Fzn_model
module E = Fzn_env

module Reg = Fzn_registry

module Slv = Solver
(*
let tok_str = function
  | Kwd k -> "{KWD}"
  | Id s -> s
  | Str s -> "\"" ^ s ^ "\""
  | Int i -> string_of_int i
  | Bool b -> if b then "true" else "false"
  *)

let put = Format.fprintf

let print_array f fmt arr = 
  put fmt "@[[" ;
  if Array.length arr > 0 then
    begin
      f fmt arr.(0) ;
      for i = 1 to Array.length arr - 1 do
        put fmt ",@ " ;
        f fmt arr.(i)
      done
    end ;
  put fmt "@]]"

let print_expr fmt assign env expr =
  let eval_ivar v = Slv.int_value assign (env.E.ivars).(v)
  and eval_bvar b = Slv.atom_value assign (env.E.bvars).(b) in
  let rec aux fmt expr = 
    match expr with
    | M.Ilit k -> put fmt "%d" k
    | M.Ivar v -> put fmt "%d" (eval_ivar v)
    | M.Blit b -> if b then (put fmt "true") else (put fmt "false")
    | M.Bvar b -> if (eval_bvar b) then put fmt "true" else put fmt "false"
    | M.Arr a -> print_array aux fmt a
  in
  aux fmt expr

let print_assign model env assign =
  Hashtbl.iter (fun id expr ->
    Format.printf "%s = " id;
    print_expr Format.std_formatter assign env expr ;
    Format.printf ";@."
  ) model.M.symbols

(*
let get_bounds ds =
  let rec aux acc u ds =
    match ds with
    | [] -> (u, List.rev acc)
    | ((l', u') :: ds') ->
      let acc' = 
        if u+1 < l' then
          (u+1, l'-1) :: acc
        else
          acc in
      aux acc' u' ds'
  in
  match ds with
  | [] -> (1, 0, [])
  | ((lb, u) :: ds) ->
    let (ub, holes) = aux [] u ds in
    (lb, ub, holes)

let create_ivar solver dom =
  match dom with
  | None -> failwith "Unbounded integer"
  | Some ds ->
    let lb, ub, holes = get_bounds ds in
    let v = Slv.new_intvar solver lb ub in
    List.iter (fun (l, r) ->
      ignore
        (Slv.post_clause solver [|Slv.ivar_lt v l ; Slv.ivar_gt v r|])
    ) holes ;
    v

let create_vars solver model = 
  let ivars = Array.map
    (* (fun _ -> Slv.new_intvar solver 0 10) *)
    (fun dom -> create_ivar solver dom)
    (Dy.to_array model.M.ivals) in
  let bvars = Array.map
    (fun _ -> Slv.new_boolvar solver)
    (Dy.to_array model.M.bvals) in
  (ivars, bvars)
*)

let post_constraint env id args =
  try
    Reg.post env id args
  with Reg.Unknown_constraint id ->
    Format.fprintf Format.err_formatter "Missing constraint: %s\n" id ;
    true

let post_constraints env model =
  Dy.fold_left
    (fun b (id, args) -> b && post_constraint env id args)
    true
    model.M.constraints
   
let post_fzn solver model =
  (* Post constraints *)
  (* let vars = create_vars solver model in *)
  let env = E.create solver model in
  let _ = post_constraints env model in
  env

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
    (Dy.length model.M.constraints) ;
  let solver = Slv.new_solver () in
  let env = post_fzn solver model  in
  match Slv.solve solver (-1) with
  | Slv.SAT ->
    begin
      Format.printf "SAT@." ;
      let assign = Slv.get_model solver in
      print_assign model env assign 
    end
  | Slv.UNSAT -> Format.printf "UNSAT@."
  | Slv.UNKNOWN -> Format.printf "UNKNOWN@."

let _ = main ()
