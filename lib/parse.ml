open Utils
open Varity
open Csl_sig
open Csl_expr
open Cdt_def
open Cdt_comp
open Cdt_var
open Cdt_infer

type 'a parse_res
  = Res of ('a * string)
  | Err of string
;;

let ret_res p s = Res (p, s);;
let ret_err s _ = Err s;;

exception Bad_Res of string

let no_err_res = function
  | Res (a, _) -> a
  | Err e -> raise (Bad_Res e)
;;

module ParseRes = struct
  let ( let* ) (s : 'a parse_res) (f : 'a * string -> 'b parse_res) : 'b parse_res =
    match s with
    | Res r -> f r
    | Err e -> Err e
  ;;
  let ( >>= ) = ( let* );;
end

type 'a parser = string -> 'a parse_res;;

let no : unit parser = ret_res ();;

let get_rest : string parser =
  fun s -> ret_res s s
;;

let ( >>= ) (p : 'a parser) (fp : 'a -> 'b parser) : 'b parser =
  fun s ->
    match p s with
    | Res (a, s') ->
        fp a s'
    | Err e -> Err e
;;
let ( let* ) = ( >>= );;

let ( <* ) (p1 : 'a parser) (p2 : 'b parser) : 'a parser =
  let open ParseRes in
  fun s ->
    let* (a, r) = p1 s in
    let* (_, r) = p2 r in
    ret_res a r
;;

let ( *> ) (p1 : 'a parser) (p2 : 'b parser) : 'b parser =
  fun s ->
    let open ParseRes in
    let* (_, r) = p1 s in
    let* (a, r) = p2 r in
    ret_res a r
;;

let ( <$ ) (a : 'a) (p : 'b parser) : 'a parser =
  let open ParseRes in
  fun s ->
    let* (_, r) = p s in
    ret_res a r
;;

let ( $> ) (p : 'a parser) (b : 'b) : 'b parser =
  fun s ->
    let open ParseRes in
    let* (_, r) = p s in
    ret_res b r
;;

let ( <$> ) (f : 'a -> 'b) (p : 'a parser) : 'b parser =
  fun s ->
    let open ParseRes in
    let* (a, r) = p s in
    ret_res (f a) r
;;

let ( <|> ) (p1 : 'a parser) (p2 : 'a parser) : 'a parser =
  fun s ->
    match p1 s with
    | Res (a, r) -> Res (a, r)
    | Err _ -> p2 s
;;

let rec many (p : 'a parser) : 'a list parser =
  many1 p <|> ret_res []

and many1 (p : 'a parser) : 'a list parser =
  let* f = p in
  let* r = many p in
  ret_res (f :: r)
;;

let ( <?> ) (pred : 'a -> bool) (p : 'a parser) : 'a parser =
  let* a = p in
  if pred a then
    ret_res a
  else
    let* r = get_rest in
    ret_err ("Fail: predicate not satisfied. ^ " ^ r)
;;

module SC = Set.Make(Char)

let str_to_list s = s |> String.to_seq |> List.of_seq;;
let list_to_str l = l |> List.to_seq |> String.of_seq;;

let pc : char parser =
  fun s ->
    match str_to_list s with
    | [] -> Err "Fail to parse char: end of the stream."
    | x :: xs ->
        ret_res x (list_to_str xs)
;;

let pcs (sc : SC.t) : char parser =
  (fun c -> SC.mem c sc) <?> pc
;;

let pcc (c : char) : char parser =
  ((==) c) <?> pc
;;

let ps (s : string) : string parser =
  let l = str_to_list s in
  let pl = l |> List.map ((<$) () << pcc) in
  List.fold_left ( *> ) no pl $> s
;;

let space_set = SC.of_list [' '; '\t'; '\r'; '\n';];;

let psp : unit parser =
  many (pcs space_set) $> ()
;;

let psp1 : unit parser =
  many1 (pcs space_set) $> ()
;;

let no_sp (p : 'a parser) : 'a parser =
  psp *> p <* psp
;;

let spec_char = SC.union (SC.of_list [','; '('; ')'; '-'; '>'; ':'; ';'; '.'; '=';]) space_set;;

module SS = Set.Make(String)

let resv = SS.of_list ["left"; "right"; "with"; "is"; "end"; "var"; "let"; "simp";];;

let pidt : string parser =
  let pc' = (fun c -> not (SC.mem c spec_char)) <?> pc in
  (fun s -> not (SS.mem s resv)) <?> (list_to_str <$> many1 pc')
;;

let p_sep_char (c : char) (p : 'a parser) : 'a list parser =
  let p' =
    let* f = p in
    let* r = many (pcc c *> p) in
    ret_res (f :: r)
  in
  p' <|> ret_res []
;;

type pre_cfe =
  | PCFE_pi of string
  | PCFE_apply of (string * pre_cfe list)
;;

let rec pp_pre_cfe = function
  | PCFE_pi s -> print_string s
  | PCFE_apply (f, l) -> 
      print_string (f ^ " ( ");
      pp_between pp_pre_cfe ", " l;
      print_string " )";
;;

module MS = Map.Make(String)

let rec restore_cfe tbl tbl_pp m = function
  | PCFE_pi s -> (
      match MS.find_opt s m with
      | Some i -> CFE_pi i
      | None -> restore_cfe tbl tbl_pp m (PCFE_apply (s, []))
  )
  | PCFE_apply (f, l) ->
      let id =
        tbl_pp.pp_fct_tbl
        |> MI.to_list
        |> List.find (fun (_, s) -> compare f s == 0)
        |> fst
      in
      CFE_apply ((get_def_by_id tbl id).fct, l |> List.map (restore_cfe tbl tbl_pp m))
;;

let p_cfe =
  let rec p_cfe' : unit -> pre_cfe parser = fun () ->
    let* idt = no_sp pidt in
    let pn =
      let* _ = no_sp (pcc '(') in
      let* l = p_sep_char ',' (no_sp (p_cfe' ())) in
      let* _ = no_sp (pcc ')') in
      ret_res l
    in
    ((fun l -> PCFE_apply (idt, l)) <$> pn) <|> ret_res (PCFE_pi idt)
  in
  p_cfe' ()
;;

let dummy_nat = {id = 0; lhs = CFE_pi 0; rhs = CFE_pi 0; argn = 0; pos = 0;};;

let p_def prefix (tbl, tbl_pp) =
  let* dir = (Left_obj <$ (psp *> ps "left")) <|> (Right_obj <$ (psp *> ps "right")) in
  let* _ = psp1 in
  let* fct_name = psp *> pidt in
  let pargl1 =
    let* _ = no_sp (pcc '(') in
    let* argl = p_sep_char ',' (no_sp pidt) in
    let* _ = psp *> pcc ')' in
    ret_res argl
  in
  let* argl = pargl1 <|> ret_res [] in
  let* _ = psp1 in
  let* _ = psp *> ps "with" in
  let* fac_name = no_sp pidt in
  let* _ = psp *> ps "is" in
  let* _ = psp1 in
  let pnat =
    let* nat_name = no_sp pidt in
    let* _ = no_sp (pcc ':') in
    let* lhs = p_cfe in
    let* _ = no_sp (ps "->") in
    let* rhs = p_cfe in
    let* _ = no_sp (pcc ';') in
    ret_res (nat_name, (lhs, rhs))
  in
  let* nats = psp *> many pnat in
  let* _ = psp *> (ps "end") in
  let m = ((fct_name, 1) :: (List.mapi (fun i a -> (a, Int.add i 2)) argl)) |> MS.of_list in
  let id = (MI.to_list tbl) |> List.map fst |> List.fold_left max 0 |> Int.add 1 in
  let argn = List.length argl in
  let (natppl, nats') = List.mapi (
    fun i (name, (l, r)) ->
      (((id, Int.add i 1), name), {
        id = id;
        lhs = restore_cfe tbl tbl_pp m l;
        rhs = restore_cfe tbl tbl_pp m r;
        argn = argn;
        pos = Int.add i 1;
      })
  ) nats |> List.split
  in
  let fac' = {
    id = id;
    args = nats';
    ret = dummy_nat;
    argn = Int.add argn 1;
  } 
  in
  let fct' = {id = id; vars = []; argn = argn;} in
  let def = {
    fct = fct';
    nats = nats';
    fac = fac';
    dir = dir;
    id = id;
  }
  in
  let pp_fct_tbl' = MI.add id fct_name tbl_pp.pp_fct_tbl in
  let pp_fac_tbl' = MI.add id fac_name tbl_pp.pp_fac_tbl in
  let ff acc (k, v) =
    Utils.MII.add k v acc
  in
  let pp_nat_tbl' = List.fold_left ff tbl_pp.pp_nat_tbl natppl in
  let tbl_pp' = {
    pp_fct_tbl = pp_fct_tbl';
    pp_nat_tbl = pp_nat_tbl';
    pp_fac_tbl = pp_fac_tbl';
    pp_var_tbl = tbl_pp.pp_var_tbl;
    pp_let_tbl = tbl_pp.pp_let_tbl;
  }
  in
  let tbl' = MI.add id def tbl in
  let () = 
    print_string (prefix ^ "> ");
    begin
      match def.dir with
      | Left_obj -> print_string "left object ";
      | Right_obj -> print_string "right object ";
    end;
    print_string fct_name;
    let vars = fct_get_var tbl' id in
    if not (List.is_empty vars) then
      begin
        print_string "(";
        pp_between pp_varity ", " vars;
        print_endline ") defined.";
      end
    else
      print_endline " defined.";
  in
  ret_res (tbl', tbl_pp')
;;

let p_file prefix (tbl, tbl_pp) =
  let p_file' =
    let rec p_file_rec (ct, ctp) =
      let p =
        let* _ = psp1 in
        let* (ct', ctp') = p_def prefix (ct, ctp) in
        p_file_rec (ct', ctp')
      in
      p <|> ret_res (ct, ctp)
    in
    let* (ct, ctp) = p_def prefix (tbl, tbl_pp) in
    p_file_rec (ct, ctp)
  in
  p_file' <|> ret_res (tbl, tbl_pp)
;;

let p_var tbl_pp =
  let* _ = psp *> ps "var" in
  let* _ = psp1 in
  let* i = psp *> pidt in
  let* _ = psp *> pcc ';' in
  let id = tbl_pp.pp_var_tbl |> MI.to_list |> List.map fst |> List.fold_left max 0 |> Int.add 1 in
  print_endline (i ^ " defined.");
  ret_res {
      pp_fct_tbl = tbl_pp.pp_fct_tbl; 
      pp_nat_tbl = tbl_pp.pp_nat_tbl; 
      pp_fac_tbl = tbl_pp.pp_fac_tbl; 
      pp_var_tbl = MI.add id i tbl_pp.pp_var_tbl;
      pp_let_tbl = tbl_pp.pp_let_tbl;
  }
;;

module OM = struct
  let ( <|> ) a b =
    match a with
    | Some _ -> a
    | None -> b
  ;;
end;;

let p_simp ((tbl, tbl_pp) : int cdt_def MI.t * int csl_expr pp_tbl) : int csl_expr parser =
  let rec p_simp1' : unit -> int csl_expr parser = fun () ->
    let* l = p_sep_char '.' (no_sp (p_simp2' ())) in
    match l with
    | [] ->
        ret_res Exp_iden
    | [x] -> 
        ret_res x
    | _ -> 
        ret_res (Exp_comp l)

  and p_simp2' : unit -> int csl_expr parser = fun () ->
    let* hd = no_sp pidt in
    let p =
      let* _ = no_sp (pcc '(') in
      let* l = p_sep_char ',' (no_sp (p_simp1' ())) in
      let* _ = no_sp (pcc ')') in
      ret_res l
    in
    let* l = (Option.some <$> p) <|> ret_res Option.none in
    match l with
    | None -> (
        let fk v ll =
          List.find_opt (fun (_, a) -> compare v a == 0) ll
          |> Option.map fst
        in
        let r =
          let open OM in
          (fk hd (Utils.MI.to_list tbl_pp.pp_fct_tbl)
            |> Option.map (fun i -> Exp_fct ((get_def_by_id tbl i).fct, [])))
          <|>
          (fk hd (Utils.MII.to_list tbl_pp.pp_nat_tbl)
            |> Option.map (fun (i, j) -> Exp_nat (List.nth (get_def_by_id tbl i).nats (Int.sub j 1))))
          <|>
          (fk hd (Utils.MI.to_list tbl_pp.pp_fac_tbl)
            |> Option.map (fun i -> Exp_fac ((get_def_by_id tbl i).fac, [])))
          <|>
          ( Utils.MS.find_opt hd tbl_pp.pp_let_tbl)
          <|>
          (fk hd (Utils.MI.to_list tbl_pp.pp_var_tbl)
            |> Option.map (fun i -> Exp_var i))
          <|>
          (fk hd [(), "I"]
            |> Option.map (fun () -> Exp_iden))
        in
        match r with
        | Some ce ->
            ret_res ce
        | None ->
            ret_err "Invalid CSL expression."
    )
    | Some ll -> (
        let fk v ll =
          List.find_opt (fun (_, a) -> compare v a == 0) ll
          |> Option.map fst
        in
        let r =
          let open OM in
          (fk hd (Utils.MI.to_list tbl_pp.pp_fct_tbl)
            |> Option.map (fun i -> Exp_fct ((get_def_by_id tbl i).fct, ll)))
          <|>
          (fk hd (Utils.MI.to_list tbl_pp.pp_fac_tbl)
            |> Option.map (fun i -> Exp_fac ((get_def_by_id tbl i).fac, ll)))
        in
        match r with
        | Some ce ->
            ret_res ce
        | None ->
            ret_err "Invalid CSL expression."
    )
  in
  p_simp1' ()
;;

let p_simp_prm (tbl, tbl_pp) =
  let* _ = psp *> ps "simp" in
  let* _ = psp1 in
  let* res = p_simp (tbl, tbl_pp) in
  let* _ = psp *> pcc ';' in
  ret_res res
;;

let p_let (tbl, tbl_pp, tbl') =
  let* _ = psp *> ps "let" in
  let* _ = psp1 in
  let* i = psp *> pidt in
  let* _ = no_sp (pcc '=') in
  let* str = no_sp (many1 ((fun c -> (not (SC.mem c spec_char)) || SC.mem c space_set || SC.mem c (SC.of_list ['.'; ','; '('; ')';])) <?> pc)) in
  let* _ = psp *> pcc ';' in
  match (no_sp (p_simp (tbl, tbl_pp))) (list_to_str str) with
  | Res (ce, rr) -> (
      if String.length rr == 0 then
        match infer_ce_ann false tbl_pp tbl' ce with
        | Some ae -> 
            print_string (i ^ " : ");
            CHI.pp_cfe_tbl tbl_pp ae.src;
            print_string " -> ";
            CHI.pp_cfe_tbl tbl_pp ae.tgt;
            print_endline " defined.";
            ret_res {
                pp_fct_tbl = tbl_pp.pp_fct_tbl; 
                pp_nat_tbl = tbl_pp.pp_nat_tbl; 
                pp_fac_tbl = tbl_pp.pp_fac_tbl; 
                pp_var_tbl = tbl_pp.pp_var_tbl;
                pp_let_tbl = MS.add i ce tbl_pp.pp_let_tbl;
            }
        | None ->
            ret_err "Invalid CSL expression. Fail to infer type."
      else
        ret_err "Invalid CSL expression."
  )
  | Err e ->
      ret_err e
;;

let p_line prefix (tbl, tbl_pp, tbl') =
  let handle_simp ce =
    let ( let* ) = Option.bind in
    let* res = comp_pair tbl {rest = ce; curr = Exp_iden;} in
    let* ae = infer_ce_ann true tbl_pp tbl' res in 
    CsHI.pp_csl_expr_tbl tbl_pp print_int res;
    print_string "\n : ";
    CHI.pp_cfe_tbl tbl_pp ae.src;
    print_string " -> ";
    CHI.pp_cfe_tbl tbl_pp ae.tgt;
    print_endline "";
    Some tbl_pp
  in
  let handle_var = Option.some in
  let handle_let = Option.some in
  let handle_all = function
    | Some a -> ret_res a
    | None -> ret_err "Invalid CSL expression."
  in
  print_string (prefix ^ "> ");
  (handle_simp <$> p_simp_prm (tbl, tbl_pp)) <|>
  (handle_var <$> p_var tbl_pp) <|>
  (handle_let <$> p_let (tbl, tbl_pp, tbl')) >>= handle_all
;;

