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

let prune_intvar s x dom =
  match dom with
  | Dom.Range (l, u) ->
    Sol.post_atom s (Sol.ivar_ge x l) && Sol.post_atom s (Sol.ivar_le x u)
  | Dom.Set ks -> Sol.make_sparse x (Array.of_list ks)

type env = { ivars : Sol.intvar array ; bvars : Atom.atom array }

let print_atom problem env =
  (* Build translation table *)
  let ivar_names = H.create 17 in
  let atom_names = H.create 17 in
  Dy.iteri (fun idx info ->
    H.add ivar_names (Sol.ivar_pred env.ivars.(idx)) info.Pr.id
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

let linterm k x = (k, x)
let neg_coeff (k, x) = (-k, x)

let apply_lindef s ctx z ts k =
  let terms =
    Array.append
      [| linterm (-1) z |]
      (Array.map (fun (k, x) -> linterm k x) ts) in
  if (* ctx.Pol.neg *) true then
    ignore @@ B.linear_le s At.at_True terms (- k) ;
  if (* ctx.Pol.pos *) true then
    ignore @@ B.linear_le s At.at_True (Array.map neg_coeff terms) k
    (*
  ignore @@ B.linear_le s At.at_True (Array.map neg_coeff terms)
  *)


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
    | Simp.Iv_opp x -> Sol.intvar_neg (make_ivar x)
    | Simp.Iv_lin ([|1, x|], k) ->
      let x' = make_ivar x in
      (* Format.fprintf Format.err_formatter "[.] := [%d] + %d@." x k ; *)
      (* let _ = prune_intvar s x' (Dom.add dom (-k)) in *)
      Sol.intvar_plus x' k
    | Simp.Iv_lin ([|-1, x|], k) ->
      let x' = make_ivar x in
      (* Format.fprintf Format.err_formatter "[.] := -[%d] + %d@." x k ; *)
      let _ = prune_intvar s x' (Dom.neg (Dom.add dom (-k))) in
      Sol.intvar_plus (Sol.intvar_neg x') k
    | _ -> make_intvar s dom in
  let _ = match Simp.map_idef make_bvar make_ivar def with
    (* Should instead resolve const references *)
    | ( Simp.Iv_none
      | Simp.Iv_const _
      | Simp.Iv_eq _
      | Simp.Iv_lin ([|1, _|], _)
      | Simp.Iv_lin ([|-1, _|], _)
      ) -> ()
    | Simp.Iv_opp x -> ()
    (* Arithmetic functions *)
    | Simp.Iv_elem (ys, x) -> failwith "Implement"
    | Simp.Iv_lin (ts, k) -> apply_lindef s ctx z ts k
    | Simp.Iv_prod ys -> failwith "Implement"
    | Simp.Iv_b2i b -> 
      ignore @@ 
      (Sol.post_clause s [| Sol.ivar_ge z 1 ; At.neg b |] &&
       Sol.post_clause s [| Sol.ivar_le z 0 ; b |])
    | Simp.Iv_max xs -> apply_max s ctx z xs
    | Simp.Iv_min xs -> apply_min s ctx z xs
  in
  let _ = prune_intvar s z dom in
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
        (* Format.fprintf Format.err_formatter "b%d := %s@." bv (Simp.string_of_bdefn bdefs.(bv)) ; *)
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
  | Pr.Ann_call ("seq_search", args) | Pr.Ann_call ("warm_start_array", args) ->
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
  | Pr.Ann_call ("warm_start", args) ->
    let xs = force_array_ivars env solver (Pr.resolve_ann problem args.(0)) in
    let cs = Pr.get_array Pr.get_int (Pr.resolve_ann problem args.(1)) in
    assert (Array.length xs = Array.length cs) ;
    Sol.warmstart_brancher
      (Array.init (Array.length xs) (fun i -> Sol.ivar_eq xs.(i) cs.(i)))
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
      Sol.toggle_brancher [|b; Sol.get_brancher solver|]
    else
      b
  in
  match parse_branchings problem env solver anns with
  | [] -> ()
  | [b] ->  Sol.add_brancher solver (wrap b)
  | bs ->
    let b = Sol.seq_brancher (Array.of_list bs) in
     Sol.add_brancher solver (wrap b)

(* Helpers for printing arrays *)
let print_fzn_array p_expr fmt es dims =
(*
  Format.fprintf fmt "array%dd(@[" (Array.length dims) ;
  Util.print_array Pr.print_ann ~sep:",@ " ~pre:"@[" ~post:"@]" fmt dims ;
  Format.fprintf fmt ",@ " ;
  Util.print_array p_expr ~sep:",@ " ~pre:"[@[" ~post:"@]]" fmt es ;
  Format.fprintf fmt "@])"
  *)
  Format.fprintf fmt "array%dd(" (Array.length dims) ;
  Util.print_array Pr.print_ann ~sep:", " ~pre:"" ~post:"" fmt dims ;
  Format.fprintf fmt ", " ;
  Util.print_array p_expr ~sep:", " ~pre:"[" ~post:"]" fmt es ;
  Format.fprintf fmt ")"


(* Print a variable assignment *)
let get_array_dims e_anns =
  match Pr.ann_call_args e_anns "output_array" with
  | Some [| Pr.Ann_arr dims |] -> dims
  | _ -> failwith "Malformed array dimensions"

let print_binding fmt id expr e_anns =
  let rec aux fmt expr =
    match expr with
    | Pr.Ilit v -> Format.pp_print_int fmt v
    | Pr.Blit b -> Format.pp_print_string fmt (if b then "true" else "false")
    | Pr.Arr es -> print_fzn_array aux fmt es (get_array_dims e_anns)
          (* Util.print_array ~sep:"," ~pre:"[@[" ~post:"@]]" aux fmt es *)
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
  
let is_output_id problem id =
  try
    let (_, anns) = Hashtbl.find problem.Pr.symbols id in
    Pr.ann_has_id anns "output_var" || Pr.ann_has_call anns "output_array"    
  with Not_found -> false

let print_solution fmt problem env model =
  if !Opts.check then
    Check.check_exn problem env.ivars env.bvars model
  else () ;
  Hashtbl.iter (fun id (expr, anns) ->
                if is_output_id problem id || is_output problem expr anns then
                  print_binding fmt id (eval_expr env model expr) anns
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
      Format.fprintf fmt "==========@."
    end
  else
    match Sol.solve solver !Opts.limits with
    | Sol.UNKNOWN -> Format.fprintf fmt "UNKNOWN@."
    | Sol.UNSAT ->
      begin
        if List.length assumps > 0 then
          let nogood = Sol.get_conflict solver in
          print_nogood fmt nogood
      end ; 
      Format.fprintf fmt "==========@."
    | Sol.SAT -> print_model fmt (Sol.get_model solver)

let solve_findall print_model print_nogood block_solution solver assumps =
  let fmt = Format.std_formatter in
  let rec aux max_sols =
    match Sol.solve solver !Opts.limits with
    | Sol.UNKNOWN -> ()
    | Sol.UNSAT -> Format.fprintf fmt "==========@."
    | Sol.SAT ->
       begin
         let model = Sol.get_model solver in
         print_model fmt model ;
         if max_sols <> 1 then
           if block_solution solver model then
             aux (max 0 (max_sols-1))
           else
             Format.fprintf fmt "==========@." 
       end
  in
  if not (apply_assumps solver assumps) then
    Format.fprintf fmt "==========@."
  else
    aux !Opts.max_solutions
          
let decrease_ivar obj_val ivar solver model =
  let model_val = Sol.int_value model ivar in
  (* Format.fprintf Format.err_formatter "%% [[OBJ = %d]]@." model_val ;  *)
  obj_val := Some model_val ;
  Sol.post_atom solver (Sol.ivar_lt ivar model_val)
      
let increase_ivar obj_val ivar solver model =
  let model_val = Sol.int_value model ivar in
  (* Format.fprintf Format.err_formatter "%% [[OBJ = %d]%@." model_val ; *)
  obj_val := Some model_val ;
  Sol.post_atom solver (Sol.ivar_gt ivar model_val)

let relative_limits solver limits =
  let s = Sol.get_statistics solver in
  { Sol.max_time =
      if limits.Sol.max_time > 0. then
        max 0.001 (limits.Sol.max_time -. s.Sol.time)
      else 0. ;
    Sol.max_conflicts =
      if limits.Sol.max_conflicts > 0 then
        max 1 (limits.Sol.max_conflicts - s.Sol.conflicts)
      else 0 }

let probe_objective solver model obj =
  (* Compute bounds *)
  match !Opts.obj_probe_limit with
  | None -> model (* Don't probe *)
  | Some probe_lim ->
    (* Set up limits for probe steps. *)
    let limits =
      let l = !Opts.limits in
      if l.Sol.max_conflicts > 0 then
        (fun () ->
          let rlim = relative_limits solver l in
          { rlim with
              Sol.max_conflicts = min probe_lim (rlim.Sol.max_conflicts) })
      else
        (fun () -> { (relative_limits solver l)
                     with Sol.max_conflicts = probe_lim })
    in
    (* Do some probing *)
    let rec aux model lb ub step =
      if lb = ub then
        model
      else begin
        let mid = max lb (ub - step) in
        if not (Sol.assume solver (Sol.ivar_le obj mid)) then
          (Sol.retract solver ; model)
        else
          match Sol.solve solver (limits ()) with
          | Sol.SAT ->
            let m' = Sol.get_model solver in 
            let ub' = Sol.int_value m' obj in
            (Sol.retract solver ; aux m' lb ub' (2*step))
          | Sol.UNSAT ->
            (Sol.retract solver ; aux model (mid+1) ub 1)
          | Sol.UNKNOWN -> (Sol.retract solver; model)
      end
    in
    aux model (Sol.ivar_lb obj) (Sol.int_value model obj) 1
      
let solve_minimize print_model print_nogood solver obj assumps =
  assert (List.length assumps = 0) ;
  let fmt = Format.std_formatter in
  let limits =
    let l = !Opts.limits in
    (fun () -> relative_limits solver l) in
  let rec aux model =
    (if !Opts.max_solutions < 1 then print_model fmt model) ;
    let obj_val = Sol.int_value model obj in
    if not (Sol.post_atom solver (Sol.ivar_lt obj obj_val)) then
      (begin
        if !Opts.max_solutions > 0 then
          print_model fmt model
       end ;
       Format.fprintf fmt "==========@." ;
       model)
    else
      match Sol.solve solver (limits ()) with
      | Sol.UNKNOWN ->
         (begin
            if !Opts.max_solutions > 0 then
              print_model fmt model
            end ;
          Format.fprintf fmt "INCOMPLETE@." ;
          model)
      | Sol.UNSAT ->
         ((* print_model fmt model ; *)
          begin
            if !Opts.max_solutions > 0 then
              print_model fmt model
            end ;
          Format.fprintf fmt "==========@." ;
          model)
      | Sol.SAT ->
        (* )
        aux (Sol.get_model solver)
        ( *)
        let m' = probe_objective solver (Sol.get_model solver) obj in
        aux m'
        (* *)
  in
  match Sol.solve solver !Opts.limits with
  | Sol.UNKNOWN -> (Format.fprintf fmt "UNKNOWN@." ; None)
  | Sol.UNSAT ->
    (* Format.fprintf fmt "UNSAT@." *)
    (Format.fprintf fmt "==========@." ; None)
  | Sol.SAT ->
    (* Some (aux (Sol.get_model solver)) *)
    Some (aux (probe_objective solver (Sol.get_model solver) obj))

type ovar_state = {
  coeff : int ;
  lb : int ;
  residual : int ;
}

let init_thresholds solver obj =
  let thresholds = H.create 17 in
  let min = ref 0 in
  List.iter (fun (c, x) -> 
    let l = Sol.ivar_lb x in
    min := !min + c * l ;
    H.add thresholds x { coeff = c ; lb = l ; residual = c ; }
  ) obj ;
  !min, thresholds

let adjust_ovar_state st k = 
  assert (k <= st.residual) ;
  if k < st.residual then
    { st with residual = st.residual - k }
  else
    { coeff = st.coeff ;
      lb = st.lb+1 ;
      residual = st.coeff; }

let update_thresholds thresholds bounds =
  let delta = Array.fold_left (fun d (x, b) ->
    let st = H.find thresholds x in
    assert (b > st.lb) ;
    min d st.residual) max_int bounds in
  Array.iter (fun (x, _) ->
    let st = H.find thresholds x in
    H.replace thresholds x (adjust_ovar_state st delta)) bounds ;
  delta

let post_thresholds solver thresholds =
  H.fold (fun x t r -> r && Sol.assume solver (Sol.ivar_le x t.lb)) thresholds true

let build_pred_map solver vars =
  let map = H.create 17 in
  List.iter (fun (_, x) -> H.add map (Sol.ivar_pred x) x) vars ;
  map

let lb_of_atom pred_map at =
  (* Find the var corresponding to the atom. *)
  let pred = at.At.pid in
  let x = H.find pred_map pred in
  let at0 = Sol.ivar_ge x 0 in
  assert (at0.At.pid = pred) ;
  let delta = Int64.sub at.At.value at0.At.value in
  (x, Int64.to_int delta)
  
let post_bool_sum_geq_ solver r bs =
  let xs = Array.map (fun b ->
    let x = Sol.new_intvar solver 0 1 in
    let at = Sol.ivar_ge x 1 in
    let _ = Sol.post_clause solver [|b ; At.neg at|] in
    let _ = Sol.post_clause solver [|At.neg b ; at|] in
    1, x) bs in
  B.linear_le solver At.at_True (Array.append [|-1, r|] xs) 0

let post_bool_sum_geq solver r bs : bool =
  B.bool_linear_ge solver r (Array.map (fun b -> 1, b) bs) 0
  
let process_core solver pred_map thresholds core =
  if Array.length core = 1 then
    let _ = Format.fprintf Format.err_formatter "%% singleton@." in
    let (x, b) = lb_of_atom pred_map core.(0) in
    let st = H.find thresholds x in
    let cost = st.residual + st.coeff * (b - st.lb - 1) in
    let _ = H.replace thresholds x { coeff = st.coeff ; lb = b ; residual = st.coeff } in
    let okay = Sol.post_atom solver core.(0) in
    assert okay ;
    cost
  else
    begin
      (* Create penalty var *)
      let p = Sol.new_intvar solver 0 (Array.length core - 1) in
      (* Relate penalty to core *)
      let _ = post_bool_sum_geq solver (Sol.intvar_plus p 1) core in
      (* let _ = post_bool_sum_geq_ solver (Sol.intvar_plus p 1) core in *)
      (* Now update thresholds *)
      let bounds = Array.map (lb_of_atom pred_map) core in    
      let delta = update_thresholds thresholds bounds in
      H.add pred_map (Sol.ivar_pred p) p ;
      H.add thresholds p { coeff = delta ; lb = 0 ; residual = delta ; } ;
      delta
    end


let log_core_iter =
  let iters = ref 0 in
  (fun lb ->
    incr iters ;
    Format.fprintf Format.err_formatter "%% Unsat core iteration: %d (lb %d).@." !iters lb)

let try_thresholds solver thresholds =
  if post_thresholds solver thresholds then
    let limits = relative_limits solver !Opts.limits in
    Sol.solve solver limits
  else
    Sol.UNSAT

let rec solve_core' print_nogood solver pred_map thresholds lb =
  log_core_iter lb ;
  (* let okay = post_thresholds solver thresholds in
  let limits = relative_limits solver !Opts.limits in
  match Sol.solve solver limits with *)
  match try_thresholds solver thresholds with
  | Sol.SAT ->
    begin
      let m = Sol.get_model solver in
      Sol.retract_all solver ;
      Some m
    end
  | Sol.UNSAT -> 
    let core = Sol.get_conflict solver in
    begin
      (* print_nogood Format.err_formatter core ; *)
      Sol.retract_all solver ;
      let delta = process_core solver pred_map thresholds core in
      solve_core' print_nogood solver pred_map thresholds (lb + delta)
    end
  | Sol.UNKNOWN ->
    begin
      Sol.retract_all solver ;
      None
    end

type core_result = 
  | Sat of Sol.model
  | Opt of Sol.model
  | Unsat
  | Unknown

let solve_core print_nogood solver obj =
  (* Post penalty thresholds *)
  let limits () = relative_limits solver !Opts.limits in
  match Sol.solve solver (limits ()) with
  | Sol.SAT ->
    (* Found a first model. *)
    let m = Sol.get_model solver in
    begin
      (* Thresholds records how much of each 
       * variable is 'free'. *)
      let pred_map = build_pred_map solver obj in
      let obj_lb, thresholds = init_thresholds solver obj in
      match solve_core' print_nogood solver pred_map thresholds obj_lb with
      | Some m' -> Opt m'
      | None -> Sat m
    end
  | Sol.UNSAT -> Unsat
  | Sol.UNKNOWN -> Unknown
 
let print_stats fmt stats obj_val =
  match !Opts.print_stats with
  | Opts.Suppress -> ()
  | Opts.Compact ->  
    begin
      Format.fprintf fmt "%d,%d,%d,%d,%d,%.02f@."
        (match obj_val with
          | Some k -> k
          | None -> 0)
        stats.Sol.solutions
        stats.Sol.restarts
        stats.Sol.conflicts
        stats.Sol.num_learnts
        stats.Sol.time
    end
  | Opts.Verbose ->
    begin
      let _ = match obj_val with
      | Some k -> Format.fprintf fmt "objective %d@." k
      | None -> ()
      in
      Format.fprintf fmt "%d solutions, %d conflicts, %d restarts@." stats.Sol.solutions stats.Sol.conflicts stats.Sol.restarts ;
      Format.fprintf fmt "%.02f seconds.@." stats.Sol.time ;
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

let minimize_uc print_model print_nogood solver obj xs =
    let fmt = Format.std_formatter in
    (* Format.fprintf fmt "[ k = %d ]@." k ; *)
    match solve_core print_nogood solver (Array.to_list xs) with
    | Sat m ->
      (print_model fmt m ;
       Format.fprintf fmt "----------@." ;
       Some m)
    | Opt m ->
      (print_model fmt m ;
       Format.fprintf fmt "==========@." ;
       Some m)
    | Unsat ->
       (Format.fprintf fmt "==========@." ; None)
    | Unknown -> None

let minimize_linear print_model print_nogood solver obj ts =
  if !Opts.core_opt then
    (* Solve using unsat cores. *)
    let xs = Array.map (fun (c, x) ->
      if c > 0 then
        c, x
      else
        -c, Sol.intvar_neg x) ts in
    minimize_uc print_model print_nogood solver obj xs
  else
    solve_minimize print_model print_nogood solver obj []

let main () =
  (* Parse the command-line arguments *)
  Arg.parse
    Opts.speclist
      (begin fun infile -> Opts.infile := Some infile end)
      "fzn_geas <options> <inputfile>"
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
  let opts = get_options () in
  let solver = Sol.new_solver opts in
  (* Construct the problem *)
  (*
  let problem =
    if !Opts.half_reify then
      Half_reify.half_reify ~ctxs:pol_ctxs problem 
    else problem in
  *)
  let (idefs, bdefs, problem) = s_problem in
  (* Simp.log_reprs idefs bdefs ; *)
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
          Format.fprintf fmt "----------@."
        end) in
  let print_nogood = print_nogood problem env in
  let obj_val = ref None in
  begin
  match fst problem.Pr.objective with
  | Pr.Satisfy ->
     if !Opts.max_solutions = 1 then
        solve_satisfy print_model print_nogood solver assumps
     else
       let block = block_solution problem env in
       solve_findall print_model print_nogood block solver assumps
  | Pr.Minimize obj ->
      let r : Sol.model option = match idefs.(obj) with
        | Simp.Iv_lin (ts, k) ->
          let xs = Array.map (fun (c, x) -> c, env.ivars.(x)) ts in
          minimize_linear print_model print_nogood solver env.ivars.(obj) xs
        | _ ->
          solve_minimize print_model print_nogood solver env.ivars.(obj) []
      in
      begin
      match r with
      | Some m -> obj_val := Some (Sol.int_value m env.ivars.(obj))
      | None -> ()
      end
  | Pr.Maximize obj ->
      let r = match idefs.(obj) with
        | Simp.Iv_lin (ts, k) ->
          let xs = Array.map (fun (c, x) -> -c, env.ivars.(x)) ts in
          minimize_linear print_model print_nogood solver (Sol.intvar_neg env.ivars.(obj)) xs
        | _ ->
          solve_minimize print_model print_nogood solver (Sol.intvar_neg env.ivars.(obj)) []
      in
      begin
      match r with
      | Some m -> obj_val := Some (Sol.int_value m env.ivars.(obj))
      | None -> ()
      end
  end ;
  (* let fmt = Format.std_formatter in *)
  let fmt = Format.err_formatter in
  print_stats fmt (Sol.get_statistics solver) !obj_val

let _ = main ()
