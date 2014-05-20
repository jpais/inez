open Core.Std ;;
open Lt_script ;;

let n =
  if not !Sys.interactive && Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    10 ;;

let f =
  let init _ = ~free
  and f f = let f' _ = ~free in Fn.compose f' f in
  Fn.apply_n_times ~n f init ;;

assert_axiom
  (~forall a (~forall b ([a <= b], f a <= f b))) ;;

let a = fresh_int_var () ;;

let b = fresh_int_var () ;;

constrain (~logic (f a > f b)) ;;

constrain (~logic (a <= b)) ;;

solve_print_result () ;;

let ideref_print id v =
  match ideref v with
  | Some i ->
    Printf.printf "%s = %s\n" id (Int63.to_string_hum i)
  | None ->
    () ;;

ideref_print "a" a ;;
