(* Decompositions for half-reified Boolean constraints *)
module Slv = Solver
module At = Atom
module Ar = Arith

let bool_or slv ?r:(r=At.at_True) bs =
  Solver.post_clause slv (Array.append [|At.neg r|] bs)

let bool_and slv ?r:(r=At.at_True) bs =
  Array.fold_left (fun ok b ->
    ok && Solver.post_clause slv [|At.neg r; b|]) true bs

let bool_iff slv ?r:(r=At.at_True) x y =
  List.fold_left (fun ok c -> ok && Solver.post_clause slv c) true
    [ [| At.neg r; x; At.neg y |] ;
      [| At.neg r; At.neg x; y |] ]

let bool_xor slv ?r:(r=At.at_True) x y =
  List.fold_left (fun ok c -> ok && Solver.post_clause slv c) true
    [ [| At.neg r; x; y |] ;
      [| At.neg r; At.neg x ; At.neg y |] ]

(* Update to use range equivalences.
 * Assumes all coefficients are positive --
 * this can be done, since -kx = (-k) + k(~x) *)
let bool_linear_le slv r ts k = failwith "Implement"

let bool_linear_int slv ?r:(r=At.at_True) ts rel k = failwith "Implement"
let bool_linear_var slv ?r:(r=At.at_True) ts rel v = failwith "Implement"
