type ranges = (int * int) list

type t = ranges option

let range lb ub = Some [lb, ub]
let free = None

let dedup ks =
  let rec aux x ys acc =
    match ys with
    | [] -> List.rev (x :: acc)
    | y :: ys' ->
      if x = y then
        aux x ys' acc
      else
        aux y ys' (x :: acc)
  in match (List.sort compare ks) with
  | [] -> []
  | x :: xs -> aux x xs []
    
let set ks = Some (List.map (fun x -> (x, x)) (dedup ks))

let intersect =
  let rec aux xs ys acc =
    match xs, ys with
    | (lx, ux) :: xs', (ly, uy) :: ys' ->
      if ly < lx then (* Out of order *)
        aux ((ly, uy) :: ys') ((lx, ux) :: xs') acc
      else
        if ux < ly then
          (* No overlap with first interval *)
          aux xs' ((ly, uy) :: ys') acc
        else
          (* Some overlap starting from ly *)
          if uy < ux then
            (* y ends before x *)
            aux ((lx, ux) :: xs') ys' ((ly, uy) :: acc)
          else
            (* x ends no later than y *)
            aux xs' ((ly, uy) :: ys') ((ly, ux) :: acc)
    | _, _ -> List.rev acc
  in fun dx dy ->
    match dx, dy with
    | None, _ -> dy
    | _, None -> dx
    | Some xs, Some ys -> Some (aux xs ys [])
