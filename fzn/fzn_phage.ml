module S = Stream
module H = Hashtbl
module Dy = DynArray

module U = Util

open Token
module P = Parser

module Pr = Problem
module Simp = Simplify
module Pol = Polarity

module Sol = Solver
module At = Atom

module B = Builtins

exception Unknown_constraint of string

let put = Format.fprintf

let get_idom model x =
 let vinfo = Dy.get model.Pr.ivals x in
 vinfo.Pr.dom

let make_intvar solver dom =
  let lb, ub = Dom.bounds dom in
  (* Create the var *)
  let v = Sol.new_intvar solver lb ub in
  (* Punch any holes. post_clause should never fail here. *)
  let _ =
    match dom with
    | Dom.Set ks -> ignore (Sol.make_sparse v (Array.of_list ks))
    | _ -> () in
  (* Then return the constructed variable *)
  v

type env = { ivars : Sol.intvar array ; bvars : Atom.atom array }

let print_atom problem env =
  (* Build translation table *)
  let ivar_names = H.create 17 in
  let atom_names = H.create 17 in
  Dy.iteri (fun idx info ->
    H.add ivar_names (Sol.ivar_pid env.ivars.(idx)) info.Pr.id
  ) problem.Pr.ivals ;
  Dy.iteri (fun idx (id, _) -> H.add atom_names env.bvars.(idx) id) problem.Pr.bvals ;
  (* Now, the actual function *)
  (fun fmt at ->
    try
      let id = H.find ivar_names at.At.pid in
      Format.fprintf fmt "%s >= %s" id (Int64.to_string @@ At.to_int at.At.value)
    with Not_found -> try
      let id = H.find ivar_names (Int32.logxor at.At.pid Int32.one) in
      Format.fprintf fmt "%s <= %s" id (Int64.to_string @@ At.to_int @@ At.inv at.At.value)
    with Not_found -> try
      let id = H.find atom_names at in
      Format.fprintf fmt "%s" id
    with Not_found -> try
      let id = H.find atom_names (At.neg at) in
      Format.fprintf fmt "not %s" id
    with Not_found -> Format.fprintf fmt "??")

let print_nogood problem env =
  let pp_atom = print_atom problem env in
  (fun fmt nogood ->
    Util.print_array ~pre:"%% @[[" ~post:"]@]@." ~sep:",@ " pp_atom fmt nogood)

(* Replace variable identifiers with the corresponding
 * intvar/atom *)
let rec resolve_expr env expr =
  match expr with
  | Pr.Ilit v -> Pr.Ilit v
  | Pr.Ivar iv -> Pr.Ivar env.ivars.(iv)
  | Pr.Blit b -> Pr.Blit b
  | Pr.Bvar bv -> Pr.Bvar env.bvars.(bv)
  | Pr.Set dom -> Pr.Set dom
  | Pr.Arr es -> Pr.Arr (Array.map (resolve_expr env) es)

(* Evaluate an expression under a model *)
let rec eval_expr env model expr =
  match expr with
  | Pr.Ilit v -> Pr.Ilit v
  | Pr.Ivar iv -> Pr.Ilit (Sol.int_value model env.ivars.(iv))
  | Pr.Blit b -> Pr.Blit b
  | Pr.Bvar bv -> Pr.Blit (Sol.atom_value model env.bvars.(bv))
  | Pr.Set dom -> Pr.Set dom
  | Pr.Arr es -> Pr.Arr (Array.map (eval_expr env model) es)

let expr_array = function
  | Pr.Arr es -> es
  | _ -> failwith "Expected array" 
               
let post_constraint solver env ident exprs anns = 
  try
    (* let handler = H.find registry ident in *)
    let handler = Registry.lookup ident in
    let args = Array.map (resolve_expr env) exprs in
    handler solver args anns
  with
  | Pr.Type_mismatch ->
    (Format.fprintf Format.err_formatter "Error: type mismatch in '%s'.@." ident ;
        false)
  | Not_found ->
    (* raise (Unknown_constraint ident) *)
    (Format.fprintf Format.err_formatter "Warning: Ignoring unknown constraint '%s'.@." ident ;
     Registry.register ident (fun _ _ _ -> true) ;
        true)

let rel_fun = function
  | Simp.Ile -> Sol.ivar_le
  | Simp.Ieq -> Sol.ivar_eq
  | Simp.Igt -> Sol.ivar_gt
  | Simp.Ine -> Sol.ivar_ne

type 'a val_inst =
  | Pending
  | Open
  | Closed of 'a

let linterm k x = { B.ic = k ; B.ix = x }
let neg_coeff t = { B.ic = -t.B.ic; B.ix = t.B.ix }

let apply_lindef s ctx z ts =
  let terms =
    Array.append
      [| linterm (-1) z |]
      (Array.map (fun (k, x) -> linterm k x) ts) in
  if ctx.Pol.neg then
    ignore @@ B.linear_le s At.at_True terms 0 ;
  if ctx.Pol.pos then
    ignore @@ B.linear_le s At.at_True (Array.map neg_coeff terms) 0

let apply_max s ctx z xs =
  match ctx with
  | { Pol.pos = true ; Pol.neg = _ } ->
    (* TODO: Add one-sided max propagator. *)
    ignore @@ B.int_max s At.at_True z xs
  | { Pol.pos = false ; Pol.neg = true } ->
    Array.iter (fun x -> ignore @@ B.int_le s At.at_True x z 0) xs
  | _ -> ()

let apply_min s ctx z xs =
  match ctx with
  | { Pol.pos = _; Pol.neg = true } ->
    failwith "TODO: Implement min propagator."
  | { Pol.pos = true; Pol.neg = false } ->
    Array.iter (fun x -> ignore @@ B.int_le s At.at_True z x 0) xs
  | _ -> ()

let build_idef s make_ivar make_bvar dom ctx def =
  let z =
    match def with
    | Simp.Iv_eq x -> make_ivar x
    | _ -> make_intvar s dom in
  let _ = match Simp.map_idef make_bvar make_ivar def with
    (* Should instead resolve const references *)
    | ( Simp.Iv_none
      | Simp.Iv_const _
      | Simp.Iv_eq _ ) -> ()
    | Simp.Iv_opp x -> apply_lindef s ctx z [| (-1, x) |]
    (* Arithmetic functions *)
    | Simp.Iv_lin ts -> apply_lindef s ctx z ts
    | Simp.Iv_prod ys -> failwith "Implement"
    | Simp.Iv_b2i b -> 
      ignore @@ 
      (Sol.post_clause s [| Sol.ivar_ge z 1 ; At.neg b |] &&
       Sol.post_clause s [| Sol.ivar_le z 0 ; b |])
    | Simp.Iv_max xs -> apply_max s ctx z xs
    | Simp.Iv_min xs -> apply_min s ctx z xs
  in
  z

let build_bdef s make_ivar make_bvar ctx def =
  match Simp.map_bdef make_bvar make_ivar def with
  | Simp.Bv_none -> Sol.new_boolvar s
  | Simp.Bv_const b -> if b then At.at_True else (At.neg At.at_True)
  | Simp.Bv_eq b -> b
  | Simp.Bv_neg b -> At.neg b
  | Simp.At (x, r, k) -> rel_fun r x k
  | Simp.Bv_or xs ->
    let z = Sol.new_boolvar s in
    begin
      if ctx.Pol.pos then
        ignore @@ Sol.post_clause s (Array.append [|At.neg z|] xs)
      else () ;
      if ctx.Pol.neg then
        Array.iter (fun x -> ignore @@ Sol.post_clause s [|z ; At.neg x|]) xs
      else () ;
      z
    end
  | Simp.Bv_and xs ->
    let z = Sol.new_boolvar s in
    begin
      if ctx.Pol.pos then
        Array.iter (fun x -> ignore @@ Sol.post_clause s [|At.neg z ; x|]) xs
      else () ;
      if ctx.Pol.neg then
        ignore @@ Sol.post_clause s (Array.append [|z|] (Array.map At.neg xs))
      else () ;
      z
    end

let make_vars s model ctxs idefs bdefs =
  let ivars = Array.make (Array.length idefs) Pending in
  let bvars = Array.make (Array.length bdefs) Pending in
  let rec make_ivar iv =
    match ivars.(iv) with
    | Closed v -> v
    | Open -> failwith "Error: cyclic definitions."
    | Pending ->
      begin
        ivars.(iv) <- Open ;
        let dom = get_idom model iv in
        let ctx = ctxs.Pol.ivars.(iv) in
        let def = idefs.(iv) in
        let v = build_idef s make_ivar make_bvar dom ctx def in
        ivars.(iv) <- Closed v ;
        v
      end
  and make_bvar bv =
    match bvars.(bv) with
    | Closed v -> v
    | Open -> failwith "Error: cyclic definitions." 
    | Pending ->
      begin
        bvars.(bv) <- Open ;
        let ctx = ctxs.Pol.bvars.(bv) in
        let v = build_bdef s make_ivar make_bvar ctx bdefs.(bv) in
        bvars.(bv) <- Closed v ;
        v
      end
  in
  (Array.init (Array.length idefs) make_ivar,
   Array.init (Array.length bdefs) make_bvar)
(*
let make_atoms s ivars bdefs =
  let bvars = Array.make (Array.length bdefs) At.at_True in
  Array.iteri (fun i _ ->
    bvars.(i) <-
      match bdefs.(i) with
      | None -> Sol.new_boolvar s
      | Some (Simp.Bv_eq v) -> bvars.(v)
      | Some (Simp.Bv_neg v) -> At.neg bvars.(v)
      | Some (Simp.At (iv, rel, k)) ->
        rel_fun rel ivars.(iv) k) bvars ;
  bvars
  *)

let build_problem solver problem ctxs idefs bdefs =
  (* Allocate variables *)
  (*
  let ivars =
    Array.init
      (Dy.length problem.Pr.ivals)
      (fun i ->
       let vinfo = Dy.get problem.Pr.ivals i in
       make_intvar solver vinfo.Pr.dom)
  in
  let bvars = make_atoms solver ivars bdefs in
  *)
  let ivars, bvars = make_vars solver problem ctxs idefs bdefs in
  let env = { ivars = ivars; bvars = bvars } in
  (* Process constraints *)
  Dy.iteri (fun id ((ident, expr), anns) ->
           Sol.set_cons_id solver (id+1) ;
           ignore @@ post_constraint solver env ident expr anns)
          problem.Pr.constraints ;
  (* Then, return the bindings *)
  env

let get_var_branch ann =
  match ann with
  | Pr.Ann_id "input_order" -> Sol.VAR_INORDER
  | Pr.Ann_id "first_fail" -> Sol.VAR_FIRSTFAIL
  | Pr.Ann_id "smallest" -> Sol.VAR_LEAST
  | Pr.Ann_id "largest" -> Sol.VAR_GREATEST
  | _ -> failwith "Unknown var-branch annotation."

let get_val_branch ann =
  match ann with
  | Pr.Ann_id "indomain_min" -> Sol.VAL_MIN
  | Pr.Ann_id "indomain_max" -> Sol.VAL_MAX 
  | Pr.Ann_id "indomain_split" -> Sol.VAL_SPLIT
  | Pr.Ann_id ("indomain"|"default") -> Sol.VAL_MIN
  | _ -> failwith "Unknown val-branch annotation."

let get_ann_array f ann =
  match ann with
  | Pr.Ann_arr xs -> Array.map f xs
  | _ -> failwith "Expected annotation array."

let collect_array_ivars env expr =
  let vars = 
    match expr with
    | Pr.Arr es ->
      List.rev @@ Array.fold_left (fun vs e ->
        match e with
        | Pr.Ivar v -> env.ivars.(v) :: vs
        | _ -> vs) [] es
    | _ -> failwith "Expected array in collect_array_ivars"
    in
    Array.of_list vars

let force_array_ivars env solver expr =
  match expr with
  | Pr.Arr es -> Array.map (fun e ->
    match e with
    | Pr.Ivar v -> env.ivars.(v)
    | Pr.Ilit k -> Solver.new_intvar solver k k
    | _ -> failwith "Expected value of int-kind in force_array_ivars") es
  | _ -> failwith "Expected array argument to force_array_ivars"

let collect_array_bvars env expr =
  let vars = 
    match expr with
    | Pr.Arr es ->
      List.rev @@ Array.fold_left (fun vs e ->
        match e with
        | Pr.Bvar v -> env.bvars.(v) :: vs
        | _ -> vs) [] es
    | _ -> failwith "Expected array in collect_array_ivars"
    in
    Array.of_list vars

let force_array_bvars env expr =
  match expr with
  | Pr.Arr es -> Array.map (fun e ->
    match e with
    | Pr.Bvar v -> env.bvars.(v)
    | Pr.Blit b -> if b then At.at_True else At.neg At.at_True
    | _ -> failwith "Expected bool-sorted term in force_array_bvars"
    ) es
  | _ -> failwith "Expected array argument to force_array_bvars"

let is_search_ann ann =
  match ann with
  | Pr.Ann_call (("seq_search"|"int_search"|"bool_search"|"bool_priority"|"int_priority"), _) -> true
  | _ -> false

let rec parse_branching problem env solver ann =
  match ann with  
  | Pr.Ann_call ("seq_search", args) ->
      let sub = get_ann_array (fun x -> x) args.(0) in
      Sol.seq_brancher (Array.map (parse_branching problem env solver) sub)
  | Pr.Ann_call ("int_search", args) ->
      let varb = get_var_branch args.(1) in
      let valb = get_val_branch args.(2) in
      let vars = collect_array_ivars env (Pr.resolve_ann problem args.(0)) in
      Sol.new_int_brancher varb valb vars
  | Pr.Ann_call ("bool_search", args) ->
      let varb = get_var_branch args.(1) in
      let valb = get_val_branch args.(2) in
      let vars = collect_array_bvars env (Pr.resolve_ann problem args.(0)) in
      Sol.new_bool_brancher varb valb vars
  | Pr.Ann_call ("int_priority", args) ->
    let varb = get_var_branch args.(2) in
    let sel = force_array_ivars env solver (Pr.resolve_ann problem args.(0)) in
    let sub = get_ann_array (parse_branching problem env solver) args.(1) in
    Sol.new_int_priority_brancher varb sel sub
  | Pr.Ann_call ("bool_priority", args) ->
    let varb = get_var_branch args.(2) in
    let sel = force_array_bvars env (Pr.resolve_ann problem args.(0)) in
    let sub = get_ann_array (parse_branching problem env solver) args.(1) in
    Sol.new_bool_priority_brancher varb sel sub
  | _ -> failwith "Unknown search annotation"

let rec parse_branchings problem env solver anns =
  let rec aux acc anns =
    match anns with
    | [] -> List.rev acc
    | ann :: anns' ->
      if is_search_ann ann  then
        aux (parse_branching problem env solver ann :: acc) anns'
      else
        aux acc anns'
  in
  aux [] anns

(* Returns none if failed *)
let get_array_assumps env in_acc arr =
  let r_assumps = Array.fold_left
    (fun acc elt ->
      match acc, elt with
      | None, _ -> None
      | _, Pr.Blit false -> None
      | Some assumps, Pr.Blit true -> Some assumps
      | Some assumps, Pr.Bvar b -> Some (env.bvars.(b) :: assumps)
      | _ -> failwith "Non-bool in assumption.") (Some in_acc) arr in
  r_assumps

let get_ann_assumps problem env anns =
  let rec aux acc anns =
    match anns with
    | [] -> Some (List.rev acc)
    | ((Pr.Ann_call ("assume", args)) :: anns') -> 
      begin
        match get_array_assumps env acc
                (Pr.get_array (fun x -> x) (Pr.resolve_ann problem args.(0))) with
        | None -> None
        | Some acc' -> aux acc' anns'
      end
    | _ :: anns' -> aux acc anns'
  in aux [] anns
 
let build_branching problem env solver anns =
  let wrap b =
    if !Opts.free then
      Sol.limit_brancher b
    else
      b
  in
  match parse_branchings problem env solver anns with
  | [] -> ()
  | [b] ->  Sol.add_brancher solver (wrap b)
  | bs ->
    let b = Sol.seq_brancher (Array.of_list bs) in
     Sol.add_brancher solver (wrap b)

(* Print a variable assignment *)
let print_binding fmt id expr =
  let rec aux fmt expr =
    match expr with
    | Pr.Ilit v -> Format.pp_print_int fmt v
    | Pr.Blit b -> Format.pp_print_string fmt (if b then "true" else "false")
    | Pr.Arr es -> Util.print_array ~sep:"," ~pre:"[@[" ~post:"@]]" aux fmt es
    | _ -> failwith "Expected only literals in solution"
  in
  Format.fprintf fmt "%s = " id ;
  aux fmt expr ;
  Format.fprintf fmt ";@."

let is_output problem expr e_anns =
  match expr with
  | Pr.Ivar iv ->
     let info = Dy.get problem.Pr.ivals iv in
     Pr.ann_has_id info.Pr.ann "output_var"
  | Pr.Bvar bv ->
     let (_, ann) = Dy.get problem.Pr.bvals bv in
     Pr.ann_has_id ann "output_var"
  | Pr.Arr _ -> Pr.ann_has_call e_anns "output_array"
  | _ -> false
  
let print_solution fmt problem env model =
  if !Opts.check then
    Check.check_exn problem env.ivars env.bvars model
  else () ;
  Hashtbl.iter (fun id (expr, anns) ->
                if is_output problem expr anns then
                  print_binding fmt id (eval_expr env model expr)
                else
                  ()) problem.Pr.symbols

let keys tbl = Hashtbl.fold (fun k v ks -> k :: ks) tbl []
let values tbl = Hashtbl.fold (fun k v vs -> v :: vs) tbl []

let output_vars problem env : (Sol.intvar list) * (Atom.t list) =
  let out_ivars = H.create 17 in
  let out_bvars = H.create 17 in
  (* Recursively collect vars in an expression *)
  let rec collect_expr expr =
    match expr with
    | Pr.Ivar iv -> H.replace out_ivars iv env.ivars.(iv)
    | Pr.Bvar bv -> H.replace out_bvars bv env.bvars.(bv)
    | Pr.Arr es -> Array.iter collect_expr es
    | _ -> ()
  in
  (* Collect vars occuring in any output expressions *)
  Hashtbl.iter (fun id (expr, anns) ->
                if is_output problem expr anns then
                  collect_expr expr
                else
                  ()) problem.Pr.symbols ;
  (values out_ivars, values out_bvars)
  
let block_solution problem env =
  let ivars, atoms = output_vars problem env in
  fun solver model ->
  (*
    let iv_atoms =
      List.map (fun x -> Sol.ivar_ne x (Sol.int_value model x)) ivars in 
      *)
    let iv_low =
      List.map (fun x -> Sol.ivar_lt x (Sol.int_value model x)) ivars in
    let iv_high =
      List.map (fun x -> Sol.ivar_gt x (Sol.int_value model x)) ivars in
    let bv_atoms =
      List.map (fun b -> if Sol.atom_value model b then Atom.neg b else b) atoms in
    (* Sol.post_clause solver (Array.of_list (iv_atoms @ bv_atoms)) *)
    Sol.post_clause solver (Array.of_list (iv_low @ (iv_high @ bv_atoms)))
      
let apply_assumps solver assumps =
  let rec aux assumps =
    match assumps with
      | [] -> true
      | at :: assumps' ->  
        if Sol.assume solver at then
          aux assumps'
        else false
  in aux assumps

(*
let print_nogood fmt nogood =
  let print_atom fmt at =
    if (Int32.to_int at.At.pid) mod 2 == 0 then
      Format.fprintf fmt "p%s >= %s"
        (Int32.to_string (Int32.shift_right at.At.pid 1))
        (Int64.to_string (At.to_int at.At.value))
    else
      Format.fprintf fmt "p%s <= %s"
        (Int32.to_string (Int32.shift_right at.At.pid 1))
        (Int64.to_string (At.to_int @@ At.inv at.At.value))
  in
  Util.print_array ~pre:"%% @[[" ~post:"]@]@." print_atom fmt nogood
  *)
    
let solve_satisfy print_model print_nogood solver assumps =
  let fmt = Format.std_formatter in
  if not (apply_assumps solver assumps) then
    begin
      print_nogood fmt (Sol.get_conflict solver) ;
      Format.fprintf fmt "============@."
    end
  else
    match Sol.solve solver !Opts.conflict_limit with
    | Sol.UNKNOWN -> Format.fprintf fmt "UNKNOWN@."
    | Sol.UNSAT ->
      begin
        if List.length assumps > 0 then
          let nogood = Sol.get_conflict solver in
          print_nogood fmt nogood
      end ; 
      Format.fprintf fmt "============@."
    | Sol.SAT -> print_model fmt (Sol.get_model solver)

let solve_findall print_model print_nogood block_solution solver assumps =
  let fmt = Format.std_formatter in
  let rec aux max_sols =
    match Sol.solve solver !Opts.conflict_limit with
    | Sol.UNKNOWN -> ()
    | Sol.UNSAT -> Format.fprintf fmt "============@."
    | Sol.SAT ->
       begin
         let model = Sol.get_model solver in
         print_model fmt model ;
         if max_sols <> 1 then
           if block_solution solver model then
             aux (max 0 (max_sols-1))
           else
             Format.fprintf fmt "===========@." 
       end
  in
  if not (apply_assumps solver assumps) then
    Format.fprintf fmt "============@."
  else
    aux !Opts.max_solutions
          
let decrease_ivar ivar solver model =
  let model_val = Sol.int_value model ivar in
  Sol.post_atom solver (Sol.ivar_lt ivar model_val)
      
let increase_ivar ivar solver model =
  let model_val = Sol.int_value model ivar in
  Sol.post_atom solver (Sol.ivar_gt ivar model_val)

let solve_optimize print_model print_nogood constrain solver assumps =
  assert (List.length assumps = 0) ;
  let fmt = Format.std_formatter in
  let rec aux model =
    print_model fmt model ;
    if not (constrain solver model) then
      ((* print_model fmt model ; *)
       Format.fprintf fmt "============@.")
    else
      match Sol.solve solver !Opts.conflict_limit with
      | Sol.UNKNOWN ->
         ((* print_model fmt model ; *)
          Format.fprintf fmt "INCOMPLETE@.")
      | Sol.UNSAT ->
         ((* print_model fmt model ; *)
          Format.fprintf fmt "==============@.")
      | Sol.SAT -> aux (Sol.get_model solver)
  in
  match Sol.solve solver !Opts.conflict_limit with
  | Sol.UNKNOWN -> Format.fprintf fmt "UNKNOWN@."
  | Sol.UNSAT -> Format.fprintf fmt "UNSAT@."
  | Sol.SAT -> aux (Sol.get_model solver)
 
let print_stats fmt stats =
  if !Opts.print_stats then
    begin
      Format.fprintf fmt "%d solutions, %d conflicts, %d restarts@." stats.Sol.solutions stats.Sol.conflicts stats.Sol.restarts ;
      Format.fprintf fmt "%d learnts, average size %f@."
        stats.Sol.num_learnts
        ((float_of_int stats.Sol.num_learnt_lits) /. (float_of_int stats.Sol.num_learnts))
    end

let get_options () =
  let defaults = Sol.default_options () in
  let rlimit = !Opts.restart_limit in
  { defaults with
    Sol.restart_limit =
      match rlimit with
      | Some r -> r
      | None -> defaults.Sol.restart_limit }
  
let set_polarity solver env pol_info =
  Array.iteri (fun i ctx ->
    match ctx with
    | { Pol.pos = false ; Pol.neg = true } ->
      Sol.set_bool_polarity solver env.bvars.(i) false
    | { Pol.pos = true ; Pol.neg = false } ->
      Sol.set_bool_polarity solver env.bvars.(i) true
    | _ -> ()
  ) pol_info.Pol.bvars ;
  Array.iteri (fun i ctx -> 
    match ctx with
    | { Pol.pos = false ; Pol.neg = true } ->
      Sol.set_int_polarity env.ivars.(i) false
    | { Pol.pos = true ; Pol.neg = false } ->
      Sol.set_int_polarity env.ivars.(i) true
    | _ -> ()
  ) pol_info.Pol.ivars

let main () =
  (* Parse the command-line arguments *)
  Arg.parse
    Opts.speclist
      (begin fun infile -> Opts.infile := Some infile end)
      "fzn_phage <options> <inputfile>"
  ;
  Half_reify.initialize () ;
  Registry.initialize () ;
  (* Parse the program *)
  let input = match !Opts.infile with
      | None -> stdin
      | Some file -> open_in file
  in
  let lexer = P.lexer input in
  let orig_problem = P.read_problem lexer in
  (* let pol_ctxs = Polarity.polarity orig_problem in *)
  let s_problem = Simplify.simplify orig_problem in
  let ctxs = Polarity.polarity s_problem in
  let (idefs, bdefs, problem) = s_problem in
  let opts = get_options () in
  let solver = Sol.new_solver opts in
  (* Construct the problem *)
  (*
  let problem =
    if !Opts.half_reify then
      Half_reify.half_reify ~ctxs:pol_ctxs problem 
    else problem in
  *)
  let env = build_problem solver problem ctxs idefs bdefs in
  (* Perform polarity analysis, to set branching *)
  let _ = if !Opts.pol then
    set_polarity solver env ctxs in
  let assumps =
    match get_ann_assumps problem env (snd problem.Pr.objective) with
    | None -> [ At.neg At.at_True ]
    | Some atoms -> atoms
  in
  build_branching problem env solver (snd problem.Pr.objective) ;
  (*
  let problem_HR =
    if !Opts.noop then
      problem
    else
      Half_reify.half_reify problem in
   *)
  let print_model =
    (fun fmt model ->
      if not !Opts.quiet then
        begin
          print_solution fmt problem env model ;
          Format.fprintf fmt "------------@."
        end) in
  let print_nogood = print_nogood problem env in
  begin
  match fst problem.Pr.objective with
  | Pr.Satisfy ->
     if !Opts.max_solutions = 1 then
        solve_satisfy print_model print_nogood solver assumps
     else
       let block = block_solution problem env in
       solve_findall print_model print_nogood block solver assumps
  | Pr.Minimize obj ->
     solve_optimize print_model print_nogood
       (decrease_ivar env.ivars.(obj)) solver assumps
  | Pr.Maximize obj ->
     solve_optimize print_model print_nogood
       (increase_ivar env.ivars.(obj)) solver assumps
  end ;
  print_stats Format.std_formatter (Sol.get_statistics solver)

let _ = main ()
