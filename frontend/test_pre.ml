let () =
  try Topdirs.dir_directory (Sys.getenv "OCAML_TOPLEVEL_PATH")
  with Not_found -> () ;;

#use "topfind" ;;
#thread ;;
#require "core" ;;
#camlp4o ;;

#load "terminology.cmo" ;;
#load "unreachable.cmo" ;;
#load "scip_idl.cmo"
#load "scip.cmo";;
#load "util.cmo" ;;
#load "formula.cmo" ;;
#load "type.cmo" ;;
#load "id.cmo" ;;
#load "logic.cmo" ;;
#load "camlp4_maps.cmo" ;;
#load "pa_logic.cmo" ;;
#load "pre.cmo" ;;
#load "solver.cmo" ;;

open Core.Std ;;
open Script;;

let roi x = Logic.M.roi x ;;

let rderef_print id v =
  match rderef v with
  | Some i ->
    Printf.printf "%s = %s\n" id (Float.to_string_hum i)
  | None ->
    () ;;

let ideref_print id v =
  match ideref v with
  | Some i ->
    Printf.printf "%s = %s\n" id (Int63.to_string_hum i)
  | None ->
    () ;;

(*
module Id' = Id.Make (struct end) ;;
module P = Pre.Make(Id') ;;
let ctx = P.make_ctx();;
                                           
module S = Solver.Make(Scip.Scip_basic)(Id') ;;
                                                                              
let sctx = S.make_ctx (Scip.Scip_basic.make_ctx ()) ;;

type c = Id'.c

(**)

let fresh_int_var2 () =
  Logic.M.M_Var (Id'.gen_id Type.Y_Int) ;;

let fresh_real_var () =
  Logic.M.M_Var (Id'.gen_id Type.Y_Real);;

let fresh_bool_var () =
  Formula.F_Atom
    (Logic.A.A_Bool
       (Logic.M.M_Var (Id'.gen_id Type.Y_Bool))) ;;

let constrain = S.assert_formula sctx;;

let solve () =
  S.solve_real sctx;;

let minimize o = 
  match S.add_real_objective sctx o with
    | `Ok -> ()
    | `Duplicate -> raise (Invalid_argument "The problem already has an objective")

let write_ctx dir = 
  S.write_bg_ctx sctx dir

let flatten_formula g =
  P.flatten_formula ctx g ;;

let flatten_term t = 
  P.flatten_term ctx t;;

let flatten_real_term f = 
 P.flatten_real_term ctx f;;

let x  = fresh_real_var();;
let x2 = fresh_real_var();;
let y  = fresh_int_var2();;
let y2 = fresh_int_var2();;

let ideref = function
  | Logic.M.M_Var v ->
    S.deref_int sctx v
  | _ ->
    None ;;

let rderef = function
  | Logic.M.M_Var v ->
    S.deref_real sctx v
  | _ -> 
    None ;;



let rderef_print id v =
  match rderef v with
  | Some i ->
    Printf.printf "%s = %s\n" id (Float.to_string_hum i)
  | None ->
    () ;;

let ideref_print id v =
  match ideref v with
  | Some i ->
    Printf.printf "%s = %s\n" id (Int63.to_string_hum i)
  | None ->
    () ;;
*)
