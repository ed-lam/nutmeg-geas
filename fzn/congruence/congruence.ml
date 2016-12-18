(* Implementation of congruence closure *)
module H = Hashtbl
module Dy = DynArray
module Q = Queue

type const_id = int

type ('v, 'f) const =
  | Var of 'v
  | Ftor of 'f
  
type use_eqn = ( (const_id * const_id) * const_id )

type eqc_data = {
  mutable canon : const_id ; (* canonical representative *)
  eqclass : const_id Dy.t ; (* members of the equiv. class *)
  uses : use_eqn Dy.t (* other eq-classes referring to this *)
}

type ('var, 'ftor) t = {
  (* symbol table *)
  consts : (('var, 'ftor) const, const_id) H.t ;

  data : eqc_data Dy.t ; (* extra data for each eq-class *)
  def_table : (const_id * const_id, const_id) H.t ;
}

let empty c_id = {
  canon = c_id ;
  eqclass = Dy.create () ;
  uses = Dy.create ()
}

let create () = {
  consts = H.create 17 ;
  data = Dy.create () ;
  def_table = H.create 17
}

let fresh_const tbl =
  let idx = Dy.length tbl.data in
  Dy.add tbl.data (empty idx) ;
  idx

(* Canonical name is eagerly updated *)
let repr tbl x = (Dy.get tbl.data x).canon

let lookup_r tbl rx ry =
  try Some (H.find tbl.def_table (rx, ry))
  with Not_found -> None

let lookup tbl x y =
  let rx = repr tbl x
  and ry = repr tbl y in
  lookup_r tbl rx ry

let add_use tbl child use = Dy.add (Dy.get tbl.data child).uses use 

let add_app tbl x y =
  let rx = repr tbl x
  and ry = repr tbl y in
  match lookup_r tbl rx ry with
  | Some rxy -> rxy
  | None ->
    let rxy = fresh_const tbl in
    begin
      H.add tbl.def_table (rx, ry) rxy ;
      add_use tbl rx ((rx, ry), rxy) ;
      add_use tbl ry ((rx, ry), rxy) ;
      rxy
    end

let add_const tbl c =
  try H.find tbl.consts c
  with Not_found ->
    let idx = H.length tbl.consts in
    H.add tbl.consts c idx ;
    idx

let add_var tbl v = add_const tbl (Var v)

let args_const tbl args =
  let sz = Array.length args in
  let res = ref args.(sz - 1) in
  for ii = sz - 2 downto 0 do
    res := add_app tbl args.(ii) !res
  done ;
  !res

let add_fun tbl f args =
  let ftor = add_const tbl (Ftor f) in
  add_app tbl ftor (args_const tbl args)

(*
let get_canon tbl x =
  let rx = Dy.get tbl.canon x in
  if rx = x then
    rx
  else 
    begin
      let rx' = get_canon tbl rx in
      Dy.set tbl.canon x rx' ;
      rx'
    end
    *)
let get_canon tbl x = (Dy.get tbl.data x).canon

type rhs =
  | C of const_id
  | A of const_id * const_id

type eqn = const_id * rhs

let revise_to tbl pending curr_r old_r =
  let curr_data = Dy.get tbl.data curr_r
  and old_data = Dy.get tbl.data old_r in
  old_data.canon <- curr_r ;
  (* Shift members of the eqclass from old to curr *)
  Dy.iter (Dy.add curr_data.eqclass) old_data.eqclass ;
  Dy.add curr_data.eqclass old_r ;
  (* Now process the uses *)
  Dy.iter (fun ((a, b), c) -> 
    match lookup tbl a b with
    | None ->
      begin
        H.add tbl.def_table (repr tbl a, repr tbl b) c ;
        Dy.add curr_data.uses ((a, b), c) 
      end
    | Some c' -> Q.add (c, c') pending) old_data.uses  ;
  Dy.clear old_data.uses
    
let class_sz tbl r = Dy.length (Dy.get tbl.data r).eqclass

let propagate tbl pending =
  while not (Q.is_empty pending)
    do
      let (c, c') = Q.pop pending in
      let rc = repr tbl c
      and rc' = repr tbl c' in
      if rc <> rc' then
        begin
          if class_sz tbl rc' < class_sz tbl rc then
            revise_to tbl pending rc' rc
          else
            revise_to tbl pending rc rc'
        end
    done

let merge tbl x y =
  let pending = Q.create () in
  Q.add (x, y) pending ;
  propagate tbl pending
