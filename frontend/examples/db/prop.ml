open Core.Std ;;
open Db_script ;;

let state = Random.State.make [|215143; 6764; 936217; 435|] ;;

let random_int = Random.State.int state ;;

let n =
  if Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    100 ;;

let double =
  Array.length argv >= 3 && String.equal argv.(2) "--double" ;;

type ii = (
  Int,
  Real
) Schema ;;

let db =
  let f i =
    let j = if double 
            then (2.0 *. Int.to_float(i)) 
            else (1.0 +. Int.to_float(i)) in
    make_row_ii (toi i, tor j) in
  make_db_ii (match List.init n ~f with
               | _ :: d when double ->
                 d
	       | l -> 
		 l) ;;

(* there exists an employee whose salary + bonus exceeds the limit *)

constrain
  (let f (x, y : Row) =
     ~logicr (x = y) in
   ~logicr (exists (sel db f))) ;;

solve_print_result () ;;
