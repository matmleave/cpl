open Utils
open Csl_sig
open Csl_expr
open Cdt_def

type simp_pair = {
  rest : int csl_expr;
  curr : int csl_expr;
};;

let rec cfe_sub_with_ce_f f = function
  | CFE_pi j -> f j
  | CFE_apply (fct, l) ->
      Exp_fct (fct, l |> List.map (cfe_sub_with_ce_f f))
;;

let cfe_sub_with_ce_only c i ce =
  let f j =
    if i == j then
      ce
    else
      Exp_iden
  in
  cfe_sub_with_ce_f f c 
;;

let cfe_sub_with_ce_args c a =
  let f i =
    if i == 1 then
      Exp_iden
    else
      List.nth a (Int.sub i 2)
  in
  cfe_sub_with_ce_f f c
;;

let expand_fct tbl fct_id l =
  let def = get_def_by_id tbl fct_id in
  let f n =
    Exp_comp [
      cfe_sub_with_ce_args n.rhs l;
      Exp_nat n;
      cfe_sub_with_ce_args n.lhs l;
    ]
  in
  Exp_fac (def.fac, def.nats |> List.map f)
;;

let rec ce_clean_iden = function
  | Exp_comp l ->
      List.fold_left exp_comp_list Exp_iden (l |> List.map ce_clean_iden)
  | Exp_fac (fac, l) ->
      Exp_fac (fac, l |> List.map ce_clean_iden)
  | Exp_fct (fct, l) ->
      Exp_fct (fct, l |> List.map ce_clean_iden)
  | c -> c
;;

module CsHI = CslHelper(Int)

let check_def_unc def =
  def.nats
  |> List.map (fun n -> not (occ_cfe 1 n.rhs))
  |> all
;;

let rec comp_pair tbl {rest; curr;} : int csl_expr option =
  let rest = ce_clean_iden rest in
  let curr = ce_clean_iden curr in
  let ( let* ) = Option.bind in
  match rest with
  | Exp_iden -> Some curr
  | Exp_comp l ->
      let l = List.map ce_clean_iden l in
      let ff a acc =
        let* accr = acc in
        comp_pair tbl {rest = a; curr = accr;}
      in
      List.fold_right ff l (Some curr) 
  | Exp_fct (fct, l) ->
      let l = List.map ce_clean_iden l in
      let rest' = expand_fct tbl fct.id l in
      comp_pair tbl {rest = rest'; curr = curr;}
  | Exp_fac (fac, l) -> (
      let l = List.map ce_clean_iden l in
      let def = get_def_by_id tbl fac.id in
      match def.dir with
      | Left_obj -> (
          let ff (n : int csl_sig_nat) sc = 
            if n.id == fac.id then
              let eli = (List.nth def.nats (Int.sub n.pos 1)).lhs in
              let sf i =
                if i == 1 then
                  rest
                else
                  Exp_iden
              in
              let eli' = cfe_sub_with_ce_f sf eli in
              let ej = List.nth l (Int.sub n.pos 1) in
              let rest' = exp_comp_list ej eli' in
              let curr' = sc in
              comp_pair tbl {rest = rest'; curr = curr';}
            else
              None
          in
          match curr with 
          | Exp_nat n ->
              ff n Exp_iden
          | Exp_comp ((Exp_nat n) :: c)  ->
              ff n (Exp_comp c)
          | _ ->
              None
      )
      | Right_obj ->
          if check_def_unc def then
            let fe i ej =
              let ee = (List.nth def.nats i).lhs in
              match ee with
              | CFE_pi 1 ->
                  comp_pair tbl {rest = ej; curr = curr;}
              | _ ->
                  Some (exp_comp_list ej (cfe_sub_with_ce_only ee 1 curr))
            in
            let* l' = opt_list_all (List.mapi fe l) in
            Some (Exp_fac (fac, l'))
          else
            Some (exp_comp_list rest curr)
  )
  | Exp_nat n -> (
      let def = get_def_by_id tbl n.id in
      match def.dir with
      | Left_obj -> 
          Some (exp_comp_list rest curr)
      | Right_obj -> (
          let erj = n.lhs in
          let* (cl, ce) = comp_rnat tbl curr erj n.id in
          let ee = cfe_sub_with_ce_only n.rhs 1 (Exp_fac (def.fac, cl)) in
          let ej = List.nth cl (Int.sub n.pos 1) in
          comp_pair tbl {rest = exp_comp_list ee ej; curr = ce;}
      )
  )
  | Exp_var _ -> Some (exp_comp_list rest curr)

and comp_rnat tbl c' cf i = (* (ce list, ce) opt *)
  let ( let* ) = Option.bind in
  let c = ce_clean_iden c' in
  let comp (fac : int csl_sig_fac) l cc p =
    let l = List.map ce_clean_iden l in
    match p with
    | CFE_pi _ -> 
        None
    | CFE_apply (pp, lp) ->
        if pp.id == fac.id && check_prd_expr tbl p 1 then
          let (ii, ei) = List.find (fun (_, ee) -> occ_cfe 1 ee) (List.mapi (fun x y -> (Int.add x 1, y)) lp) in
          let pdef = get_def_by_id tbl pp.id in
          let npj = List.find (fun nn -> occ_cfe (Int.add ii 1) nn.rhs) pdef.nats in
          let ej = List.nth l (Int.sub npj.pos 1) in
          let* cc' = comp_pair tbl {rest = ej; curr = cc;} in
          let epj = CHI.cfe_sub_with_list [(Int.add ii 1, ei);] npj.rhs in
          let* (l', ccc) = comp_rnat tbl cc' epj i in
          let tr ii' e =
            if ii' == npj.pos then
              ccc
            else
              let eii = (List.nth pdef.nats (Int.sub ii' 1)).lhs in
              let eii' = cfe_sub_with_ce_only eii 1 cc in
              exp_comp_list e eii'
          in
          let cl' = List.mapi (fun i' x -> tr (Int.add i' 1) x) l in 
          Some (l', Exp_fac (fac, cl'))
        else
          None
  in
  match (c, cf) with
  | (Exp_fac (fac, l), CFE_pi 1) ->
      let l = List.map ce_clean_iden l in
      if fac.id == i then Some (l, Exp_iden) else None
  | (Exp_comp ((Exp_fac (fac, l)) :: rr), CFE_pi 1) ->
      let l = List.map ce_clean_iden l in
      if fac.id == i then Some (l, Exp_comp rr) else None
  | (Exp_fac (fac, l), p) ->
      let l = List.map ce_clean_iden l in
      comp fac l Exp_iden p
  | (Exp_comp ((Exp_fac (fac, l)) :: rr), p) ->
      let l = List.map ce_clean_iden l in
      comp fac l (Exp_comp rr) p
  | _ ->
      None
;;
