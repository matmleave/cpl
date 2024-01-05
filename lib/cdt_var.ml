open Varity
open Csl_sig
open Cdt_def

let rec fct_get_var tbl id =
  let def = get_def_by_id tbl id in
  let f i =
    let vl = 
      def.nats 
      |> List.map (fun n -> (cfe_get_var tbl n.lhs i, cfe_get_var tbl n.rhs i))
    in
    match def.dir with
    | Left_obj ->
        var_left vl
    | Right_obj ->
        var_right vl
  in
  let nl = Seq.ints 2 |> Seq.take def.fct.argn |> List.of_seq in
  List.map f nl

and cfe_get_var tbl c i =
  let rec f cc cr acc =
    match cc with
    | CFE_pi j ->
        if j == i then
          cr + acc
        else
          acc
    | CFE_apply (fct, l) ->
        let fv = fct_get_var tbl fct.id in
        let z = List.combine fv l in
        List.fold_left (fun ac (v, a) -> f a (v * cr) ac) acc z 
  in
  f c Var_pos Var_bot
;;
