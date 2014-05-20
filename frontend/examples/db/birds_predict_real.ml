open Core.Std ;;
open Db_script ;;

(* initializing random number generator *)

let state = Random.State.make [|15038; 19624; 31779; 2891; 13009|] ;;

let random_int = Random.State.int state ;;

let random_real = Random.State.float state ;;

(* input *)

let n =
  if Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    1000 ;;

assert (n >= 0 && n % 100 = 0) ;;

let n_types =
  if Array.length argv >= 3 then
    int_of_string argv.(2)
  else
    10 ;;

let unsat =
  if Array.length argv >= 4 then
    argv.(3) = "--unsat"
  else
    false ;;

assert (n_types >= 0) ;;

(* Schema *)

type observation = (
  Real,  (* timestamp *)
  Int,   (* bird type ID *)
  Real,  (* longitude (X) *)
  Real,  (* latitude (Y) *)
  Int    (* observation ID *)
) Schema ;;

let point_noise = 10.0 ;;

(* departure from Mexico *)

let x_orig = - 100.45_00  ;;  (* inclusive *)

let y_orig =    20.12_00  ;;  (* exclusive *)

(* now in Pennsylvania *)

let x_now  = -  80.79_00  ;;  (* inclusive *)

let y_now  =    40.53_00  ;;  (* exclusive *)


(* wrappers around RNG *)

let random_x_around x =
  (x -. point_noise) +. random_real (2.0 *. point_noise +. 1.0) ;;

let random_y_around y =
  (y -. point_noise) +. random_real (2.0 *. point_noise +. 1.0) ;;

let random_pair_around (x, y) =
  random_x_around x, random_y_around y ;;

let random_point_for_t t =
  random_pair_around
    (x_orig +. (x_now -. x_orig) *. t /. 100.0,
     y_orig +. (y_now -. y_orig) *. t /. 100.0) ;;

let random_type () =
  random_int n_types ;;

let l_observations =
  let f i =
    let t = Int.to_float (i / (n / 100)) in
    let p = random_type ()
    and x, y = random_point_for_t t in
    make_row_observation (tor t, toi p, tor x, tor y, toi i) in
  List.init n ~f ;;

let l_observations =
  if unsat then
    l_observations
  else
    let f i =
      let t = fresh_real_var ()
      and p = fresh_int_var ()
      and x = fresh_real_var ()
      and y = fresh_real_var ()
      and i = toi (n + i) in
      constrain (~logicr (x >. tor x_now && y >. tor y_now &&
                           t >. 100.0 &&
                           p >= 0 && p <= toi n_types));
      make_row_observation (t, p, x, y, i) in
    List.init 5 ~f @ l_observations ;;

let observations = make_db_observation l_observations ;;


let oo =
  ~logicr
    (sel (cross observations observations)
       (fun (_, p , _, _, _,
             _, p', _, _, _ : Row) ->
         p = p')) ;;

let ooo =
  ~logicr
    (sel (cross oo observations)
       (fun (_, p , _, _, _,
             _, _ , _, _, _,
             _, p', _, _, _ : Row) ->
         p = p')) ;;

constrain
  (~logicr
      (exists
         (sel ooo
            (fun ((t0 : Real), _, (x0 : Real), (y0 : Real), _,
                  (t1 : Real), _, (x1 : Real), (y1 : Real), _,
                  (t2 : Real), _, (x2 : Real), (y2 : Real), _ : Row) ->
                x2 >. tor x_now && y2 >. tor y_now &&
                t2 >. 100.0 && 100.0 >. t1 && t1 >. t0 &&
                x2 >=. x1 && x1 >=. x0 &&
                y2 >=. y1 && y1 >=. y0 &&
                2.0 *. (t2 -. t0) <=. 5.0 *. (t1 -. t0) &&
                2.0 *. (t2 -. t0) >=. 3.0 *. (t1 -. t0) &&
                2.0 *. (x2 -. x0) <=. 5.0 *. (x1 -. x0) &&
                2.0 *. (x2 -. x0) >=. 3.0 *. (x1 -. x0) &&
                2.0 *. (y2 -. y0) <=. 5.0 *. (y1 -. y0) &&
                2.0 *. (y2 -. y0) >=. 3.0 *. (y1 -. y0))))) ;;

solve_print_result () ;;
