let rec list_perm l =
    match l with
    | [] -> [[]]
    | x :: xs ->
           (let lp = list_perm xs in
            let rec f sl sr =
                match sr with
                | [] -> [List.append sl [x]]
                | r :: rs ->
                        (List.append sl (x :: sr)) ::
                            (f (List.append sl [r]) rs)
            in
            List.map (fun s -> f [] s) lp
            |> List.concat)
;;

let rec any = function
    | [] -> false
    | x :: xs -> if x then true else any xs
;;

let rec all = function
    | [] -> true
    | x :: xs -> if x then all xs else false
;;

let ( << ) f g =
    fun x -> f (g x)

    
let pp_list pp m =
    Printf.printf "[ ";
    List.iter (fun x -> pp x; Printf.printf "; ") m;
    Printf.printf "]";
;;

module E (Ord1 : Map.OrderedType) (Ord2 : Map.OrderedType) = struct
    type t = Left of Ord1.t | Right of Ord2.t
    let left x = Left x
    let right x = Right x
    let compare = compare
    let pp_e ppl ppr = function
        | Left l -> Printf.printf "Left "; ppl l
        | Right r -> Printf.printf "Right "; ppr r
    let (==) e1 e2 = (compare e1 e2) == 0
end

let pp_option pp = function
    | Some x -> Printf.printf "Some "; pp x
    | None -> Printf.printf "None";;

let pp_tuple ppa ppb = function
    | (a, b) -> Printf.printf "("; ppa a; Printf.printf ", "; ppb b; Printf.printf ")";;

module MapHelper (M : Map.S) = struct
    let comb_map m1 m2 =
        let rec comb l1 m2 =
            match l1 with
            | [] -> m2
            | (_, []) :: lxs -> comb lxs m2
            | (lxi, lxc :: lxcs) :: lxs ->
                    (comb ((lxi, lxcs) :: lxs) m2)
                    |> M.add_to_list lxi lxc 
        in
        comb (M.to_list m1) m2

    let pp_map ppk ppv m =
        Printf.printf "[ ";
        M.iter (fun k v -> ppk k; Printf.printf " -> "; ppv v; Printf.printf "; ") m;
        Printf.printf "]";
end

let tuple_f (f1, f2) (x1, x2) = (f1 x1, f2 x2);;

let id x = x;;

let rec opt_list_all = function
    | [] -> Some []
    | (Some x) :: xs ->
            let ( let* ) = Option.bind in
            let* fs = opt_list_all xs in
            Some (x :: fs)
    | None :: _ -> None
;;

let rec pp_between pp str = function
  | [] -> ();
  | [x] -> pp x;
  | x :: y :: r -> pp x; print_string str; pp_between pp str (y :: r);
;;

module MI = Map.Make(Int);;

module II = struct
  type t = int * int;;
  let compare = compare;;
end;;

module MII = Map.Make(II);;
module MS = Map.Make(String);;

type 'a pp_tbl = {
  pp_fct_tbl : string MI.t;
  pp_nat_tbl : string MII.t;
  pp_fac_tbl : string MI.t;
  pp_var_tbl : string MI.t;
  pp_let_tbl : 'a MS.t;
};;

let empty_pp_tbl = {
  pp_fct_tbl = MI.empty;
  pp_nat_tbl = MII.empty;
  pp_fac_tbl = MI.empty;
  pp_var_tbl = MI.empty;
  pp_let_tbl = MS.empty;
};;
