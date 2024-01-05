open Varity
open Utils

(* $ pi var, @ fct, & nat, # fac *)

type csl_sig_fct = {
    id : int;
    vars : varity list;
    argn : int;
};;

type 'a cfe
    = CFE_apply of (csl_sig_fct * ('a cfe list))
    | CFE_pi of 'a
;;

type 'a csl_sig_nat = {
    id : int;
    lhs : 'a cfe;
    rhs : 'a cfe;
    argn : int;
    pos : int;
};;

type 'a csl_sig_fac = {
    id : int;
    args : 'a csl_sig_nat list;
    ret : 'a csl_sig_nat;
    argn : int;
};;

module CfeHelper (Ord : Map.OrderedType) = struct

    module SS = Set.Make(Ord);;

    let rec pp_cfe_tbl tbl = function
      | CFE_pi i -> Printf.printf "X%d" i
      | CFE_apply (fct, l) -> 
          let module MI = Map.Make(Int) in
          print_string (MI.find fct.id tbl.pp_fct_tbl);
          if List.is_empty l then ()
          else begin
            print_string "("; pp_between (pp_cfe_tbl tbl) ", " l; print_string ")";
          end;
    ;;

    let cfe_args c =
        let rec collect c s =
            match c with
            | CFE_pi i -> SS.add i s
            | CFE_apply (_, []) -> s
            | CFE_apply (f, x :: xs) ->
                    s
                    |> collect x
                    |> collect (CFE_apply (f, xs)) 
        in
        collect c SS.empty |> SS.to_seq |> List.of_seq
    ;;

    module MM = Map.Make(Ord);;

    let cfe_perm c args targs =
        let args_perm = list_perm targs in
        let rec f ap sc =
            let m = List.combine args ap |> List.to_seq |> MM.of_seq in
            match sc with
            | CFE_pi i -> (CFE_pi (MM.find i m), m)
            | CFE_apply (fct, l) -> (CFE_apply (fct, List.map (fst << (f ap)) l), m)
        in
        List.map (fun a -> f a c) args_perm
    ;;

    let pp_fct (f : csl_sig_fct) =
        Printf.printf "@%d" f.id;
    ;;
                    
    let rec pp_cfe pp = function
        | CFE_pi i -> Printf.printf "$"; pp i;
        | CFE_apply (fct, l) ->
                let rec f = function
                    | [] -> ()
                    | x :: xs -> pp_cfe pp x; Printf.printf "; "; f xs;
                in
                pp_fct fct; Printf.printf ": [ "; f l; Printf.printf "]";
    ;;

    let pp_nat pp (n : 'a csl_sig_nat) =
        Printf.printf "&%d: (" n.id;
        pp_cfe pp n.lhs;
        Printf.printf ") -> (";
        pp_cfe pp n.rhs;
        Printf.printf ")";
    ;;

    let pp_fac pp (f : 'a csl_sig_fac) =
        Printf.printf "#%d: [ " f.id;
        List.iter (fun x -> pp_nat pp x; Printf.printf "; ";) f.args;
        Printf.printf "] -> ";
        pp_nat pp f.ret;
    ;;

    let rec cfe_eq c1 c2 =
        match c1 with
        | CFE_pi i -> (
                match c2 with
                | CFE_pi j -> (Ord.compare i j) == 0
                | _ -> false)
        | CFE_apply (fct, l) -> (
                match c2 with
                | CFE_apply (fct', l') ->
                        (fct.id == fct'.id) && (List.map2 cfe_eq l l' |> all)
                | _ -> false)
    ;;

    let cfe_match c1 c2 =
        let args1 = cfe_args c1 in
        let args2 = cfe_args c2 in
        if List.length args1 != List.length args2 then None else
        let perm1 = cfe_perm c1 args1 args2 in
        let rec m = function
        | [] -> None
        | x :: xs ->
                if cfe_eq (fst x) c2 then
                    Some (snd x)
                else
                    m xs
        in
        m perm1
    ;;

    let rec cfe_map f = function
        | CFE_pi i -> CFE_pi (f i)
        | CFE_apply (fct, l) -> CFE_apply (fct, List.map (cfe_map f) l)

    let cfe_sub_with_list l c =
        let rec s ff = function
            | CFE_pi i -> ff i
            | CFE_apply (fct, ll) -> CFE_apply (fct, List.map (s ff) ll)
        in
        let f t =
            match List.find_opt (fun (i, _) -> (compare i t) == 0) l with
            | Some (_, e) -> e
            | None -> CFE_pi t
        in
        s f c

    let nat_map f (n : 'a csl_sig_nat) = {
        id = n.id;
        lhs = cfe_map f n.lhs;
        rhs = cfe_map f n.rhs;
        argn = n.argn;
        pos = n.pos;
    }

    let nat_sub_with_list l (n : 'a csl_sig_nat) = {
        id = n.id;
        lhs = cfe_sub_with_list l n.lhs;
        rhs = cfe_sub_with_list l n.rhs;
        argn = n.argn;
        pos = n.pos;
    }

    let fac_map f (fac : 'a csl_sig_fac) = {
        id = fac.id;
        args = List.map (nat_map f) fac.args;
        ret = nat_map f fac.ret;
        argn = fac.argn;
    }

    let fac_sub_with_list l (fac : 'a csl_sig_fac) = {
        id = fac.id;
        args = List.map (nat_sub_with_list l) fac.args;
        ret = nat_sub_with_list l fac.ret;
        argn = fac.argn;
    }

end

module EII = E(Int)(Int)
module MII = Map.Make(EII)
module MHII = MapHelper(MII)

open EII
module CHI = CfeHelper(Int)


let rec unify_gen c1 c2 =
    match c1 with
    | CFE_pi i -> Some (MII.of_list [(left i, [CHI.cfe_map right c2])])
    | CFE_apply (fct1, l1) -> (
            match c2 with
            | CFE_pi j -> Some (MII.of_list [(right j, [CHI.cfe_map left c1])])
            | CFE_apply (fct2, l2) -> (
                    if fct1.id != fct2.id then
                        None
                    else
                        let (let*) = Option.bind in
                        let rec f z =
                            match z with
                            | (s1, s2) :: zs ->
                                    let* res = unify_gen s1 s2 in
                                    let* ress = f zs in
                                    let module MHII = MapHelper(MII) in
                                    Some (MHII.comb_map res ress)
                            | [] -> Some MII.empty
                        in
                        f (List.combine l1 l2)
            )
    )
;;

module CFE (Ord : Map.OrderedType) = struct
    type t = Ord.t cfe
    let compare = compare
end

module CHEII = CfeHelper(EII)
module SII = Set.Make(EII)
module SCFE = Set.Make(CFE(EII))

let rec unify_gen_update c1 c2 =
    match c1 with
    | CFE_pi i -> Some (MII.of_list [(i, [c2])])
    | CFE_apply (fct1, l1) -> (
            match c2 with
            | CFE_pi j -> Some (MII.of_list [(j, [c1])])
            | CFE_apply (fct2, l2) -> (
                    if fct1.id != fct2.id then
                        None
                    else
                        let (let*) = Option.bind in
                        let rec f z =
                            match z with
                            | (s1, s2) :: zs ->
                                    let* res = unify_gen_update s1 s2 in
                                    let* ress = f zs in
                                    let module MHII = MapHelper(MII) in
                                    Some (MHII.comb_map res ress |> MII.map SCFE.of_list |> MII.map SCFE.to_list)
                            | [] -> Some MII.empty
                        in
                        f (List.combine l1 l2)
            )
    )
;;

let unify_get_dep (r : 'a cfe list MII.t) =
    let l : (EII.t * 'a cfe list) list = MII.to_list r in
    let rec f = function
        | [] -> []
        | ((a : EII.t), b) :: r ->
                let b' = List.filter (fun x -> (compare (CFE_pi a) x) != 0) b in
                (a, List.map CHEII.cfe_args b' |> List.concat |> SII.of_list |> SII.to_list) :: (f r)
    in
    MII.of_list (f l)
;;

let unify_check_dep (d : EII.t list MII.t) =
  let rec update d' =
    if MII.is_empty d' then
      true
    else
      let a = d' |> MII.to_list |> List.map snd |> List.concat |> SII.of_list |> SII.to_list in
      if List.is_empty a then
        true
      else
        let f x =
          match MII.find_opt x d' with
          | Some y -> List.is_empty y
          | None -> true
        in
        match List.find_opt f a with
        | Some x ->
            let d' = MII.remove x d' in
            let d' = d' |> MII.to_list |> List.map (fun (i, l) -> (i, List.filter (fun k -> compare k x != 0) l)) |> MII.of_list in
            update d'
        | None -> 
            false
  in
  update d

let unify_tran r =
    let ( let* ) = Option.bind in
    let rec f rr cr =
        match rr with
        | [] -> Some cr
        | (_, []) :: rs -> f rs cr
        | (lxi, [lxj]) :: rs ->
                let* res = f rs cr in
                res |> MII.add_to_list lxi lxj |> Option.some
        | (lxi, lxj :: lxk :: lxr) :: lxs ->
                if (compare (CFE_pi lxi) lxj) == 0 then
                    f ((lxi, lxk :: lxr) :: lxs) cr
                else if (compare (CFE_pi lxi) lxk) == 0 then
                    f ((lxi, lxj :: lxr) :: lxs) cr
                else
                    let* res = f ((lxi, lxj :: lxr) :: lxs) cr in
                    let* gen = unify_gen_update lxj lxk in
                    Some (MHII.comb_map res gen)
    in
    f (MII.to_list r) MII.empty
;;

let unify_check_solvable r =
    let l = MII.to_list r in
    let ( let* ) = Option.bind in
    let rec f s =
        match s with
        | [] -> Some MII.empty
        | (xi, [xj]) :: xs ->
                let* rs = f xs in 
                Some (MII.add xi xj rs)
        | _ -> None
    in
    f l
;;

let unify_topo_sort a r =
    (* m : Map EII (Set EII) *)
    let rec f m c =
        if MII.is_empty m then
            c
        else
            let l = MII.to_list m in
            let e = List.find (fun (_, s) -> SII.is_empty s) l |> fst in
            let m' = MII.remove e m in
            let mm = MII.map (SII.remove e) m' in
            match MII.find_opt e r with
            | Some er -> 
                    let ee = CHEII.cfe_sub_with_list (MII.to_list c) er in 
                    MII.add e ee c |> f mm
            | None ->
                    MII.add e (CFE_pi e) c |> f mm
    in
    let g rr =
        let m = rr |> MII.map (fun x -> [x]) |> unify_get_dep |> MII.map SII.of_list in
        let rec h r c =
            match r with
            | [] -> c
            | x :: xs ->
                    if MII.mem x c then
                        h xs c
                    else
                        h xs (MII.add x SII.empty c)
        in
        h a m
    in
    f (g r) MII.empty
;;

let pp_unify_gen_res =
    let pp1 = EII.pp_e print_int print_int in
    let pp2 = CHEII.pp_cfe pp1 in
    let pp3 = pp_list pp2 in
    let module MHII = MapHelper(MII) in
    let pp3 = MHII.pp_map pp1 pp3 in
    let pp4 = pp_option pp3 in
    pp4
;;

let pp_unify_get_dep_res =
    let pp1 = EII.pp_e print_int print_int in
    let pp3 = pp_list pp1 in
    let module MHII = MapHelper(MII) in
    let pp3 = MHII.pp_map pp1 pp3 in
    pp3
;;

let unify_clean c1 s =
    c1 |> CHEII.cfe_map left |> CHEII.cfe_sub_with_list (MII.to_list s)
;;

let unify_canon m =
    let l = MII.to_list m in
    let rec collect = function
        | [] -> []
        | (_ , c) :: xs -> List.append (CHEII.cfe_args c) (collect xs)
    in
    let a = collect l |> SII.of_list |> SII.to_list in
    let ff i _ = Int.add i 1 in
    let b = List.mapi ff a in
    let m = List.combine a b |> MII.of_list in
    let rec t = function
        | [] -> ([], [])
        | (Left i, c) :: xs -> tuple_f ((fun fxs -> (i, CHEII.cfe_map (fun x -> MII.find x m) c) :: fxs), id) (t xs)
        | (Right i, c) :: xs -> tuple_f (id, (fun fxs -> (i, CHEII.cfe_map (fun x -> MII.find x m) c) :: fxs)) (t xs)
    in
    t l
;;

let unify_solve c1 c2 =
    let ( let* ) = Option.bind in
    let a = SII.union (CHI.cfe_args c1 |> List.map left |> SII.of_list)
        (CHI.cfe_args c2 |> List.map right |> SII.of_list) |> SII.to_list in
    let rec f r =
        if not (r |> unify_get_dep |> unify_check_dep) then
            None
        else 
            match r |> unify_check_solvable with
            | Some r' -> Some (unify_topo_sort a r')
            | None ->
                    let* r' = unify_tran r in
                    f r'
    in
    let* init = unify_gen c1 c2 in
    f init
;;

let unify_solve_e c1 c2 : t cfe MII.t option =
    let ( let* ) = Option.bind in
    let a = SII.union (CHEII.cfe_args c1 |> SII.of_list)
        (CHEII.cfe_args c2 |> SII.of_list) |> SII.to_list in
    let rec f r =
        if (r |> unify_get_dep |> unify_check_dep) then
            match r |> unify_check_solvable with
            | Some r' -> Some (unify_topo_sort a r')
            | None ->
                    let* r' = unify_tran r in
                    f r'
        else
            None
    in
    let* init = unify_gen_update c1 c2 in
    f init
;;

let uni = {id = 0; vars = []; argn = 0};;
