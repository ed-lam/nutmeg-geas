module M = Fzn_model
module Slv = Solver
module Dy = DynArray

type expr = M.expr

type env = {
  solver : Solver.t ;
  ivars : Solver.intvar array ;
  bvars : Atom.t array
}

type t = env

(* Extracting data from fzn_exprs *)
let expr_array f s = function
  | M.Arr es -> Array.map (f s) es
  | _ -> failwith "Expression not an array"

let expr_ivar e = function
  | M.Ivar v -> e.ivars.(v)
  | _ -> failwith "Expression not an ivar"

let expr_bvar e = function
  | M.Bvar b -> e.bvars.(b)
  | _ -> failwith "Expression not a bvar"

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

let create solver model =
  let ivars = Array.map
    (fun dom -> create_ivar solver dom)
    (Dy.to_array model.M.ivals) in
  let bvars = Array.map
    (fun _ -> Slv.new_boolvar solver)
    (Dy.to_array model.M.bvals) in
  { solver = solver ; ivars = ivars ; bvars = bvars }

