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


(*
module P = Pre.Make (Id') ;;
let ctx2 = P.make_ctx () ;;
*)

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

(*
let e = ~logicr(0.5 *. x +. roi(4 * y + 5 * y2) +. 3.5 *. x +. 2.8 *. x2 +. roi(6 * y) =. 0.5) ;;

let e2 = ~logicr(roi(4 * y + 5 * y2) +. 3.5 *. x +. 2.8 *. x2 <=. 0.5);;
*)


let roi x = Logic.M.roi x ;;

let dedup f = P.try_dedup_real_sum f;;
