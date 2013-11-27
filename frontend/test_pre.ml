let () =
  try Topdirs.dir_directory (Sys.getenv "OCAML_TOPLEVEL_PATH")
  with Not_found -> () ;;

#use "topfind" ;;
#thread ;;
#require "core" ;;
#camlp4o ;;

#load "terminology.cmo" ;;
#load "unreachable.cmo" ;;
#load "util.cmo" ;;
#load "formula.cmo" ;;
#load "type.cmo" ;;
#load "id.cmo" ;;
#load "logic.cmo" ;;
#load "pre.cmo" ;;
#load "camlp4_maps.cmo" ;;
#load "pa_logic.cmo" ;;

open Core.Std ;;

module Id' = Id.Make (struct end) ;;
module P = Pre.Make (Id') ;;

let ctx = P.make_ctx () ;;

let fresh_int_var () =
  Logic.M.M_Var (Id'.gen_id Type.Y_Int) ;;

let fresh_real_var () =
  Logic.M.M_Var (Id'.gen_id Type.Y_Float);;

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
