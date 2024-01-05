open Utils
open Csl_sig
open Csl_expr
open Cdt_def
open Cdt_var

module MI = Map.Make(Int)

let fix_tbl tbl =
  let fix_def did def =
    let args = Seq.ints 2 |> Seq.take def.fct.argn |> List.of_seq |> List.map (fun i -> CFE_pi i)in
    let ft = CFE_apply (def.fct, args) in
    let fix_fct (fct : csl_sig_fct) =
      {
        id = did;
        vars = fct_get_var tbl did;
        argn = fct.argn;
      }
    in
    let fix_nat {id; lhs; rhs; argn; pos;} =
      let _ = id in
      let lhs' = CHI.cfe_sub_with_list [(1, ft);] lhs in
      let rhs' = CHI.cfe_sub_with_list [(1, ft);] rhs in
      {
        id = did;
        lhs = lhs';
        rhs = rhs';
        argn = argn;
        pos = pos;
      }
    in
    let fix_fac {id; args; ret; argn;} =
      let _ = (id, ret, argn) in
      let ret' =
        match def.dir with
        | Left_obj ->
            {
              id = did;
              lhs = ft;
              rhs = CFE_pi 1;
              argn = Int.add def.fct.argn 1;
              pos = 0;
            }
        | Right_obj ->
            {
              id = did;
              lhs = CFE_pi 1;
              rhs = ft;
              argn = Int.add def.fct.argn 1;
              pos = 0;
            }
      in
      {
        id = did;
        args = args;
        ret = ret';
        argn = Int.add def.fct.argn 1;
      }
    in
    let def' =
      {
        fct = def.fct |> fix_fct;
        nats = def.nats |> List.map fix_nat;
        fac = def.fac |> fix_fac;
        dir = def.dir;
        id = did;
      }
    in
    def'
  in
  MI.mapi (fun k v -> fix_def k v) tbl
;;

let rec fix_ce tbl' ce =
  match ce with
  | Exp_iden -> ce 
  | Exp_comp l -> Exp_comp (l |> List.map (fix_ce tbl'))
  | Exp_fct (f, l) -> 
      let f' = (MI.find f.id tbl').fct in
      Exp_fct (f', l |> List.map (fix_ce tbl')) 
  | Exp_nat n ->
      let n' = List.nth (MI.find n.id tbl').nats (Int.sub n.pos 1) in
      Exp_nat n';
  | Exp_fac (f, l) ->
      let f' = (MI.find f.id tbl').fac in
      Exp_fac (f', l |> List.map (fix_ce tbl'))
  | Exp_var _ -> ce
;;

module CsHI = CslHelper(Int)

let infer_ce_ann (from_one : bool) tbl_pp tbl' ce =
  let ce' = fix_ce tbl' ce in
  match tbl_pp.pp_fct_tbl |> MI.to_list |> List.find_opt (fun (_, s) -> compare s "1" == 0) with
  | Some (one_id, _) ->
      let one = (MI.find one_id tbl').fct in
      if from_one then
        csl_gen_ae_type' from_one one (exp_comp_list ce' (Exp_var 0))
      else
        csl_gen_ae_type' from_one {id = 0; vars = []; argn = 0;} ce'
  | None ->
      csl_gen_ae_type' from_one {id = 0; vars = []; argn = 0;} ce'
;;
