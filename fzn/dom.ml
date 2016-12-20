(* Representation of domains for preprocessing *)
type t =
  | Range of int * int
  | Set of int list

let range lb ub = Range (lb, ub)
let set ks = Set ks

let rappend xs ys = List.fold_left (fun s k -> k :: s) ys xs

let rec merge xs ys =
  let rec aux xs ys acc =
    match xs, ys with
    | ([], s) | (s, []) -> rappend acc s
    | x :: xs', y :: ys' ->
        if x < y then
          aux xs' ys (x :: acc) 
        else if y < x then
          aux xs ys' (y :: acc)
        else
          aux xs' ys' (x :: acc)
  in aux xs ys []

let union x y = match x, y with
  | Set kx, Set ky -> Set (merge kx ky)
  | Range (lx, ux), Range (ly, uy) ->
      Range (min lx ly, max ux uy)
  | (Range (l, u), Set k) | (Set k, Range (l, u)) ->
      Range
        ((List.fold_left min l k),
         (List.fold_left max u k))

let bounds d =
  match d with
  | Range (l, u) -> l, u
  | Set (k :: ks) -> List.fold_left min k ks, List.fold_left max k ks
  | _ -> failwith "Bounds of empty domain"

(* Compute the set of holes in a given domain *)
let holes d =
  match d with
  | Range _ -> []
  | Set ks ->
     let rec aux x ys acc =
       match ys with
       | [] -> List.rev acc
       | y :: ys' ->
          if x < y then
            aux (y+1) ys' ((x, y-1) :: acc)
          else
            aux (y+1) ys' acc
     in
     match List.sort compare ks with
     | x :: xs -> aux (x+1) xs []
     | _ -> []
