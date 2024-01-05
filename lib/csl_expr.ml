open Utils
open Varity
open Csl_sig

type 'a csl_expr
    = Exp_iden
    | Exp_comp of ('a csl_expr list)
    | Exp_nat of 'a csl_sig_nat
    | Exp_fac of ('a csl_sig_fac * ('a csl_expr list))
    | Exp_fct of (csl_sig_fct * ('a csl_expr list))
    | Exp_var of int
;;

type 'a csl_aexpr
    = AExp_iden of 'a cfe
    | AExp_comp of ('a csl_aexpr list)
    | AExp_nat of ('a csl_sig_nat * ('a cfe list))
    | AExp_fac of ('a csl_sig_fac * ('a cfe list) * ('a csl_aexpr list))
    | AExp_fct of (csl_sig_fct * ('a csl_aexpr list))
    | AExp_var of int
;;

type 'a csl_aexpr_type = {
    ae : 'a csl_aexpr;
    src : 'a cfe;
    tgt : 'a cfe;
};;

module CslHelper (Ord : Map.OrderedType) = struct

    open CfeHelper(Ord);;

    module MI = Utils.MI;;
    module MII = Utils.MII;;

    let rec pp_csl_expr_tbl trp pp = function
      | Exp_iden -> Printf.printf "I";
      | Exp_comp el -> pp_between (pp_csl_expr_tbl trp pp) "." el;
      | Exp_nat n -> print_string (Utils.MII.find (n.id, n.pos) trp.pp_nat_tbl);
      | Exp_fac (f, el) -> 
          print_string (MI.find f.id trp.pp_fac_tbl);
          if List.is_empty el then ()
          else begin
            print_string "("; pp_between (pp_csl_expr_tbl trp pp) ", " el; print_string ")";
          end;
      | Exp_fct (f, el) -> 
          print_string (MI.find f.id trp.pp_fct_tbl);
          if List.is_empty el then ()
          else begin
            print_string "("; pp_between (pp_csl_expr_tbl trp pp) ", " el; print_string ")";
          end;
      | Exp_var i -> print_string (MI.find i trp.pp_var_tbl);
    ;;

    let rec pp_csl_expr pp = function
      | Exp_iden -> Printf.printf "{I}";
      | Exp_comp el -> Printf.printf "< "; List.iter (fun c -> pp_csl_expr pp c; Printf.printf "; ";) el; Printf.printf ">";
      | Exp_nat n -> Printf.printf "Nat "; pp_nat pp n;
      | Exp_fac (f, el) -> Printf.printf "Fac "; pp_fac pp f; Printf.printf " ( "; List.iter (fun c -> pp_csl_expr pp c; Printf.printf "; ";) el; Printf.printf ")";
      | Exp_fct (f, el) -> Printf.printf "Fct "; pp_fct f; Printf.printf " ( "; List.iter (fun c -> pp_csl_expr pp c; Printf.printf "; ";) el; Printf.printf ")";
      | Exp_var i -> Printf.printf "|%d|" i;
    ;;

    let rec pp_csl_aexpr pp = function
        | AExp_iden c -> Printf.printf "AIden["; pp_cfe pp c; Printf.printf "]";
        | AExp_comp el -> Printf.printf "AComp < "; List.iter (fun c -> pp_csl_aexpr pp c; Printf.printf "; ";) el; Printf.printf ">";
        | AExp_nat (n, l) -> Printf.printf "ANat "; pp_nat pp n; Printf.printf  " ( "; List.iter (fun c -> pp_cfe pp c; Printf.printf "; ";) l; Printf.printf ")";
        | AExp_fac (f, l, el) -> Printf.printf "AFac "; pp_fac pp f; Printf.printf " ( "; List.iter (fun c -> pp_cfe pp c; Printf.printf "; ";) l; Printf.printf " ) ( "; List.iter (fun c -> pp_csl_aexpr pp c; Printf.printf "; ";) el; Printf.printf ")";
        | AExp_fct (f, el) -> Printf.printf "AFct "; pp_fct f; Printf.printf " ( "; List.iter (fun c -> pp_csl_aexpr pp c; Printf.printf "; ";) el; Printf.printf ")";
        | AExp_var i -> Printf.printf "|%d|" i;
    ;;

    let pp_csl_aexpr_type pp t =
        Printf.printf "{ ae = "; pp_csl_aexpr pp t.ae; Printf.printf " ; src = "; pp_cfe pp t.src; Printf.printf " ; tgt = "; pp_cfe pp t.tgt; Printf.printf "; }";
    ;;

    let rec csl_sub_with_list l cae =
        match cae with
        | AExp_iden c -> AExp_iden (cfe_sub_with_list l c)
        | AExp_comp el -> AExp_comp (List.map (csl_sub_with_list l) el)
        | AExp_nat (n, el) -> AExp_nat (nat_sub_with_list l n, List.map (cfe_sub_with_list l) el)
        | AExp_fac (f, el, ael) -> AExp_fac (fac_sub_with_list l f, List.map (cfe_sub_with_list l) el, List.map (csl_sub_with_list l) ael)
        | AExp_fct (f, el) -> AExp_fct (f, List.map (csl_sub_with_list l) el)
        | AExp_var _ -> cae
    ;;

    let csl_type_sub_with_list l cat = {
        ae = csl_sub_with_list l cat.ae;
        src = cfe_sub_with_list l cat.src;
        tgt = cfe_sub_with_list l cat.tgt;
    };;

    let rec csl_map (f : 'a -> 'b) cae =
        match cae with
        | AExp_iden c -> AExp_iden (cfe_map f c)
        | AExp_comp el -> AExp_comp (List.map (csl_map f) el)
        | AExp_nat (n, el) -> AExp_nat (nat_map f n, List.map (cfe_map f) el)
        | AExp_fac (fa, el, ael) -> AExp_fac (fac_map f fa, List.map (cfe_map f) el, List.map (csl_map f) ael)
        | AExp_fct (fc, el) -> AExp_fct (fc, List.map (csl_map f) el)
        | AExp_var i -> AExp_var i
    ;;

    let csl_type_map (f : 'a -> 'b) cat = {
        ae = csl_map f cat.ae;
        src = cfe_map f cat.src;
        tgt = cfe_map f cat.tgt;
    };;

end

let exp_comp_list e1 e2 =
    match (e1, e2) with
    | (Exp_iden, Exp_iden) -> Exp_iden
    | (Exp_iden, _) -> e2
    | (_, Exp_iden) -> e1
    | (Exp_comp l1, Exp_comp l2) -> Exp_comp (List.append l1 l2)
    | (Exp_comp l, _) -> Exp_comp (List.append l [e2])
    | (_, Exp_comp l) -> Exp_comp (List.append [e1] l)
    | (_, _) -> Exp_comp [e1; e2;]
;;

let aexp_comp_list ae1 ae2 =
    match (ae1, ae2) with
    | (AExp_comp l1, AExp_comp l2) -> AExp_comp (List.append l1 l2)
    | (AExp_comp l, _) -> AExp_comp (List.append l [ae2])
    | (_, AExp_comp l) -> AExp_comp (List.append [ae1] l)
    | (_, _) -> AExp_comp [ae1; ae2;]
;;

open E(Int)(Int)
open CslHelper(Int)
module MHI = MapHelper(Map.Make(Int))
module SInt = Set.Make(Int)

let csl_gen_ae_type' (from_one : bool) (one : csl_sig_fct) ce =
  let rec csl_gen_ae_type ce =
      let ( let* ) = Option.bind in
      match ce with
      | Exp_iden ->
              Some {
                  ae = AExp_iden (CFE_pi 1);
                  src = CFE_pi 1;
                  tgt = CFE_pi 1;
              }
      | Exp_comp l ->
              let cb t1' t2' =
                  let* ti1 = t1' in
                  let* ti2 = t2' in
                  let t1 = ti1 |> csl_type_map left in
                  let t2 = ti2 |> csl_type_map right in
                  let* r = unify_solve_e (CFE_apply (uni, [t1.src; t1.tgt; t2.src;])) (CFE_apply (uni, [t2.tgt; t1.tgt; t2.src;])) in
                  let l = r |> unify_canon in
                  let ae1 = csl_sub_with_list (fst l) ti1.ae in
                  let ae2 = csl_sub_with_list (snd l) ti2.ae in
                  Some {
                      ae = aexp_comp_list ae1 ae2;
                      src = CHI.cfe_sub_with_list (snd l) ti2.src;
                      tgt = CHI.cfe_sub_with_list (fst l) ti1.tgt;
                  }
              in
              let l' = List.map csl_gen_ae_type l in
              List.fold_left cb (Some {ae = AExp_comp []; src = CFE_pi 1; tgt = CFE_pi 1;}) l'
      | Exp_nat n ->
              Some {
                  ae = AExp_nat (n, Seq.ints 1 |> Seq.take n.argn |> List.of_seq |> List.map (fun x -> CFE_pi x));
                  src = n.lhs;
                  tgt = n.rhs;
              }
      | Exp_fac (fac, l) ->
              let* tl = List.map csl_gen_ae_type l |> opt_list_all in
              let rec f ll c =
                  match ll with 
                  | [] -> ([], [])
                  | x :: xs ->
                          let a = List.append (CHI.cfe_args x.src) (CHI.cfe_args x.tgt) |> List.fold_left max 0 in
                          let x' = csl_type_map (Int.add c) x in
                          let res = f xs (Int.add c a) in
                          (x' :: (fst res), c :: (snd res))
              in
              let (l', tr) = f tl 0 in
              let t = List.map (fun n -> [n.lhs; n.rhs;]) fac.args |> List.concat in
              let rt = List.map (CHEII.cfe_map right) [fac.ret.lhs; fac.ret.rhs;] in
              let ll = l' |> List.map (fun x -> [x.src; x.tgt;]) |> List.concat |> List.map (CHEII.cfe_map left) |> List.append rt in
              let tt = t |> List.map (CHEII.cfe_map right) |> List.append rt in
              let* r = unify_solve_e (CFE_apply (uni, ll)) (CFE_apply (uni, tt)) in
              let car = unify_canon r in
              let nlf i cae =
                  let c = List.nth tr i in
                  cae |> csl_type_map (Int.add c) |> csl_type_sub_with_list (fst car)
              in
              let nl = List.mapi nlf tl in
              let ann = Seq.ints 1 |> Seq.take fac.argn |> List.of_seq |> List.map (fun i -> List.find (fun (x, _) -> x == i ) (snd car) |> snd) in
              let src' = CHI.cfe_sub_with_list (snd car) fac.ret.lhs in
              let tgt' = CHI.cfe_sub_with_list (snd car) fac.ret.rhs in
              Some {
                  ae = AExp_fac (CHI.fac_sub_with_list (snd car) fac, ann, nl |> List.map (fun x -> x.ae));
                  src = src';
                  tgt = tgt';
              }
      | Exp_fct (fct, l) ->
              let fv (v, ce) =
                  match v with
                  | Var_pos ->
                          csl_gen_ae_type ce
                  | Var_bot ->
                          csl_gen_ae_type ce
                  | Var_neg ->
                          let* ct = csl_gen_ae_type ce in
                          Some {
                              ae = ct.ae;
                              src = ct.tgt;
                              tgt = ct.src;
                          }
                  | Var_top ->
                          let* ct = csl_gen_ae_type ce in
                          Some {
                              ae = AExp_iden ct.src;
                              src = ct.src;
                              tgt = ct.src;
                          }
              in
              let* r = List.combine fct.vars l |> List.map fv |> opt_list_all in
              let rec f l c =
                  match l with
                  | [] -> []
                  | x :: xs ->
                          let a = List.append (CHI.cfe_args x.src) (CHI.cfe_args x.tgt) |> List.fold_left max 0 in
                          let x' = csl_type_map (Int.add c) x in
                          x' :: (f xs (Int.add c a))
              in
              let rr = f r 0 in
              let src' = CFE_apply (fct, rr |> List.map (fun x -> x.src)) in
              let tgt' = CFE_apply (fct, rr |> List.map (fun x -> x.tgt)) in
              Some {
                  ae = AExp_fct (fct, rr |> List.map (fun x -> x.ae));
                  src = src';
                  tgt = tgt';
              }
      | Exp_var i -> 
              if from_one && i == 0 then
                  Some {
                      ae = AExp_var 0;
                      src = CFE_apply (one, []);
                      tgt = CFE_pi 1;
                  }
              else
                  Some {
                      ae = AExp_var i;
                      src = CFE_pi 1;
                      tgt = CFE_pi 2;
                  }
  in
  csl_gen_ae_type ce



