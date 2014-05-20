open Core.Std ;;
open Db_script ;;

(* initializing random number generator *)

let state = Random.State.make [|15038; 19624; 31779; 2891; 13009|] ;;

let random_int = Random.State.int state ;;

let random_real = Random.State.float state;;

(* parameters from the command line *)

let n =
  if Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    100 ;;

assert (n >= 4) ;;

let synthesize =
  Array.length argv >= 3 && argv.(2) = "--synthesize" ;;

let synthesize_unsat =
  Array.length argv >= 4 && argv.(3) = "--synthesize-unsat" ;;

(* database schema *)

(*let n = 15;;
let synthesize = true;;
let synthesize_unsat = false;;
*)

type employee = (
  Int,  (* employee ID *)
  Int,  (* age *)
  Int   (* level: 0 = junior, 1 = middle, 2 = senior *)
) Schema ;;

type bonus = (
  Int,  (* employee ID *)
  Real   (* amount *)
) Schema ;;

let base_salary = 30_000.00 ;;

let base_income age level =
  base_salary +. 20_000.00 *. (Int.to_float level) +. 500.00 *. (Int.to_float (age - 18)) ;;

let base_income_symbolic age level =
  ~logicr ((tor base_salary) +. 20_000.00 *. (Db_logic.M.M_ROI level) +. 500.00 *. (Db_logic.M.M_ROI (age - 18))) ;;

let l_employees, l_bonuses =
  let f i =
    if i < n * 3 / 4 then
      let age = 30 + random_int 36
      and level = random_int 3 in
      let base = base_income age level in
      let bonus = (max (random_real (base /. 4.0 +. 1.0)) 1.0) in
      make_row_employee (toi i, toi age, toi level),
      Some (make_row_bonus (toi i, tor bonus))
    else
      let age = 18 + random_int 12
      and level = random_int 2 in
      make_row_employee (toi i, toi age, toi level),
      None in
  List.unzip (List.init n ~f) ;;

let l_bonuses = List.filter_opt l_bonuses ;;

let employees = make_db_employee l_employees ;;

let l_bonuses =
  if synthesize || synthesize_unsat then
    let id = fresh_int_var ()
    and amount = fresh_real_var () in
    constrain (~logicr (amount >=. 0.0));
    constrain (~logicr (id >= 0));
    (let f (id', age, level : Row) =       
       ~logicr (id = id' &&
           4.0 *. amount <=. base_income_symbolic age level) in
     constrain (~logicr (exists (sel employees f))));
    make_row_bonus (id, amount) :: l_bonuses
  else
    l_bonuses ;;

 let bonuses = make_db_bonus l_bonuses ;;

 let eb =
  let f (id, _, _, id', _ : Row) = ~logicr (id = id') in
  ~logicr (sel (cross employees bonuses) f) ;;

constrain
  (let limit = tor (if synthesize_unsat then 70_000.00 else 69_000.00) in
   let f (_, age, level, _, (amount : Real) : Row) =
     ~logicr (age < 30 && 
               base_income_symbolic age level +. amount >=. limit) in
   ~logicr (exists (sel eb f))) ;;

solve_print_result () ;;
