(** Problem simplification *)
module H = Hashtbl
module Dy = DynArray

module Pr = Problem
(* Currently a no-op *)
let registry = H.create 17

let simplify_constraint id args anns =
  try
    let simplifier = H.find registry id in
    simplifier args anns
  with Not_found -> [ (id, args), anns ]

let simplify problem = problem
(*
  let constraints =
    Dy.of_list @@ List.rev @@ Dy.fold_left
      (fun acc ((id, args), anns) -> (simplify_constraint id args anns)) [] problem.Pr.constraints in
  { problem with Pr.constraints = constraints }
  *)

(*

(* Simplifier definitions *)
let array_bool_and solver args anns =
  let xs = Pr.get_array get_atom args.(0) in
  let z = get_atom args.(1) in
  Array.fold_left
    (fun b x -> b && S.post_clause solver [|At.neg z; x|])
    (S.post_clause solver
                   (Array.append [|z|] (Array.map At.neg xs))) xs

*)

(*
let simp_le pr terms k =
  let all_bool = ref true in
  let terms', k' = Array.fold_left (fun (acc, k') (c, x) ->
    match c, x with
    | Ilit c, Ilit x -> acc, k - (c*x)
    | Ilit c, Ivar v ->
      let d = Pr.dom_of pr x in
      begin
      match Dom.size d with
      | 1 -> acc, k - (c * (Dom.lb d))
      | 2 -> ((Pr.Ilit c, Pr.Ivar v) :: acc), k'
      | _ -> (all_bool := false ; ((Ilit c, Ivar v) :: acc))
      if dom_size d = 1 then
        acc, k - (c * (Dom.lb pr x))
      else
        ((Ilit c, Ivar v) :: acc), k'
    | _ -> failwith "Expected ilit or ivar") ([], k) terms in
  List.rev terms', k'
  *)

(*
let int_lin_le args anns =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array  args.(1) in
  let terms = Array.init (Array.length xs)
                         (fun i -> cs.(i) , xs.(i)) in
  let k = Pr.get_int args.(2) in
  match simp_le terms k with
  | [(1, x) ; (-1, y)], k' -> [("int_diff", [|x; y; Pr.Ilit k'|]), anns]
  | [(-1, y) ; (1, x)], k' -> [("int_diff", [|x; y; Pr.Ilit k'|]), anns]
  | terms', k' ->
    let tarr = Array.of_list terms' in
    [("int_lin_le", Pr.Arr (Array.map fst terms'), Pr.Arr (Array.map snd terms')]
  ("int_lin_le", args), anns
  *)
