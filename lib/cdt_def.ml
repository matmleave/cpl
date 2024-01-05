open Utils
open Csl_sig 

type cdt_obj_dir = Left_obj | Right_obj;;

(* first arg of each nat is F *)

type 'a cdt_def = {
  fct : csl_sig_fct;
  fac : 'a csl_sig_fac;
  nats : 'a csl_sig_nat list;
  id : int;
  dir : cdt_obj_dir;
};;

let rec occ_cfe id = function
  | CFE_pi i -> (compare i id) == 0
  | CFE_apply (_, l) -> any (l |> List.map (occ_cfe id))

open CfeHelper(Int)
module MI =  Map.Make(Int)

let get_def_by_id tbl id = MI.find id tbl

(* return the location of the only occurance of Yi in lhs *)
let rec check_prd_fct tbl id yi =
  let def = get_def_by_id tbl id in
  let ii = Int.add yi 1 in
  if def.dir == Left_obj then
    None
  else if any (def.nats |> List.map (fun x -> occ_cfe ii x.lhs)) then
    None
  else
    let cnt_f acc a =
      match acc with
      | Some (Some _) -> if occ_cfe ii a.rhs then None else acc
      | Some None -> if occ_cfe ii a.rhs then Some (Some a) else acc
      | None -> None
    in
    let cnt = List.fold_left cnt_f (Some None) def.nats in
    match cnt with
    | Some (Some a) ->
        if cfe_eq a.lhs (CFE_pi 1) then
          if check_prd_expr tbl a.rhs ii then
            Some a
          else
            None
        else
          None
    | _ -> None

and check_prd_expr tbl (c : int cfe) yi =
  match c with
  | CFE_pi i -> (compare i yi) == 0
  | CFE_apply (fct, l) ->
      let cnt_f acc a =
        match acc with
        | Some (Some _) ->
            if occ_cfe yi (snd a) then None else acc
        | Some None ->
            if occ_cfe yi (snd a) then
              if check_prd_expr tbl (snd a) yi then 
                Some (Some a)
              else
                None
            else
              Some None
        | None -> None
      in
      let res = List.fold_left cnt_f (Some None) (List.mapi (fun i a -> (Int.add i 1, a)) l) in
      match res with
      | Some (Some (i, _)) -> (
        match check_prd_fct tbl fct.id i with
        | Some _ -> true
        | _ -> false)
      | _ -> false
;;

let check_def_comp tbl id =
  let def = get_def_by_id tbl id in
  match def.dir with
  | Left_obj ->
      all (List.map (
        fun x ->
          match x.rhs with
          | CFE_pi i -> i == 1
          | CFE_apply _ -> false
      ) def.nats)
  | Right_obj ->
      all (List.map (
        fun x ->
          check_prd_expr tbl x.lhs 1
      ) def.nats)
;;
