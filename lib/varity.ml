type varity
    = Var_pos
    | Var_neg
    | Var_bot
    | Var_top
;;

let pp_varity = function
  | Var_pos -> print_string "+";
  | Var_neg -> print_string "-";
  | Var_bot -> print_string "_";
  | Var_top -> print_string "=";
;;

let ( * ) var1 var2 =
    match var1 with
    | Var_bot ->
            Var_bot
    | Var_pos ->
            var2
    | Var_neg ->
            (match var2 with
            | Var_pos ->
                    Var_neg
            | Var_neg ->
                    Var_pos
            | _ -> var2)
    | Var_top ->
            (match var2 with
            | Var_bot ->
                    Var_bot
            | _ -> Var_top)
;;

let ( <= ) var1 var2 =
    (var2 == Var_top) || (var1 == Var_bot)
;;

let ( >= ) var1 var2 = var2 <= var1;;
    
let ( + ) var1 var2 =
    if var1 <= var2 then
        var2
    else if var1 >= var2 then
        var1
    else Var_top
;;

let var_left l =
  let ff acc (v1, v2) =
    acc + (v1 + (Var_neg * v2))
  in
  List.fold_left ff Var_bot l
;;

let var_right l =
  let ff acc (v1, v2) =
    acc + ((Var_neg * v1) + v2)
  in
  List.fold_left ff Var_bot l
;;
