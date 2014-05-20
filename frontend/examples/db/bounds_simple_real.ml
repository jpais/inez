open Core.Std ;;
open Db_script ;;

(* initializing random number generator *)

let state = Random.State.make [|13633; 23193; 1230; 6800; 30314|] ;;

let random_int = Random.State.int state ;;

let random_real = Random.State.float state;;

let n =
  if Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    1000 ;;

let synthesize =
  Array.length argv >= 3 && argv.(2) = "--synthesize" ;;

type ii = (Real, Real) Schema ;;
  
let db =
  let f i = make_row_ii (~logicr (tor (Int.to_float i), 10.0 *. (tor (Int.to_float i)))) in
  let l = List.init n ~f in
  let l =
    if synthesize then
      let v = fresh_real_var () in
      let k = tor (10.0 *. (Int.to_float n)) in
      constrain (~logicr (v <. k));
      make_row_ii (~logicr (tor (Int.to_float n), v)) :: l
    else
      l in
  make_db_ii l ;;

constrain
  (let k = tor (10.0 *. (Int.to_float n)) in
   ~logicr (exists (sel db (fun (_, (v : Real) : Row) -> v >=. k)))) ;;

solve_print_result () ;;
