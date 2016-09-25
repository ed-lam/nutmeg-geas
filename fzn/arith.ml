(* Implementation of arithmetic constraints *)
module B = Builtins

type rel = Le | Ge | Lt | Gt | Eq | Ne

(* r -> sum (c_i x_i) op k *)
let to_linexpr ts = Array.map (fun t -> { B.c = fst t; B.x = snd t }) ts
let neg_terms ts = Array.map (fun t -> (- fst t, snd t)) ts

let int_linear slv ?r:(r=Atom.at_True) ts rel k =
  match rel with
  | Le -> B.linear_le slv r (to_linexpr ts) k 
  | Lt -> B.linear_le slv r (to_linexpr ts) (k-1)
  | Gt -> B.linear_le slv r (to_linexpr (neg_terms ts)) (-k+1)
  | Ge -> B.linear_le slv r (to_linexpr (neg_terms ts)) (-k)
  | Eq -> (B.linear_le slv r (to_linexpr ts) k)
            && (B.linear_le slv r (to_linexpr (neg_terms ts)) (-k))
  | Ne -> failwith "Implement"

let int_abs slv ?r:(r=Atom.at_True) z x = B.int_abs slv r z x
let int_mul slv ?r:(r=Atom.at_True) z x y = B.int_mul slv r z x y

let int_div slv ?r:(r=Atom.at_True) z x y = failwith "Implement"

let int_max slv ?r:(r=Atom.at_True) z xs = failwith "Implement"
let int_min slv ?r:(r=Atom.at_True) z xs = failwith "Implement"
