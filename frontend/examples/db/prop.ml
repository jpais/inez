open Core.Std ;;
open Db_script ;;

let state = Random.State.make [|215143; 6764; 936217; 435|] ;;

let random_int = Random.State.int state ;;

let n =
  if Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    10 ;;

let double =
  Array.length argv >= 3 && String.equal argv.(2) "--double" ;;


type ii = (
  Real,
  Real
) Schema ;;

let db =
  let f i =
    let j = if double 
            then (2.0 *. Int.to_float(i)) 
            else (1.0 +. Int.to_float(i)) in
    make_row_ii (tor (Int.to_float(i)), tor j) in
  let l = List.append (List.init n ~f) [make_row_ii (tor 3.0, tor 3.0)] in
  make_db_ii (match l with
               | _ :: d when double ->
                 d
	       | l -> 
		 l) ;;

(* there exists an employee whose salary + bonus exceeds the limit *)

constrain
  (let f ((x : Real), (y : Real) : Row) =
     ~logicr (x =. y) in
   ~logicr (exists (sel db f))) ;;

solve_print_result () ;;
