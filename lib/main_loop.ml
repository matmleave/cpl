open Utils
open Cdt_infer
open Parse

let usage = "cpl -f <file>";;
let path = ref "";;
let anon _ = ();;
let speclist = [("-f", Arg.Set_string path, "Set input file path for definitions.");];;

let start_def =
  Arg.parse speclist anon usage;
  let ch = open_in_bin !path in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  p_file (!path ^ "-info") (MI.empty, empty_pp_tbl) s
  |> no_err_res
;;

let loop (tbl, tbl_pp) =
  let tbl' = fix_tbl tbl in
  let rec loop' ctp =
    print_string "cpl> ";
    flush stdout;
    let line = input_line stdin in
    match p_line "info" (tbl, ctp, tbl') line with
    | Res (res, _) ->
        loop' res;
    | Err e ->
        print_endline e;
        loop' ctp;
  in
  loop' tbl_pp
;;
