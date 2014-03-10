module Id' = Id.Make (struct end)

module S = Db_solver.Make(Scip.Scip_with_dp)(Id')

let ctx = S.make_ctx `Lazy

type c = Id'.c

let constrain g =
  match S.assert_formula ctx g with
  | `Ok ->
    ()
  | `Out_of_fragment ->
    raise (Invalid_argument "constrain: formula out of fragment")

let minimize m =
  match S.add_objective ctx m with
  | `Ok ->
    ()
  | `Duplicate ->
    raise (Invalid_argument "problem has objective already")
  | `Out_of_fragment ->
    raise (Invalid_argument "minimize: term out of fragment")

let maximize m = 
 match S.add_objective ctx (Db_logic.M.(~- m)) with
    |`Ok -> 
      ()
    | `Duplicate ->
      raise (Invalid_argument "The problem already has an objective.")
    | `Out_of_fragment ->
      raise (Invalid_argument "Maximize: term out of fragment")

let minimize_real o =  raise (Failure "Undefined function minimize_real")

let maximize_real o = raise (Failure "Undefined function maximize_real")

let solve () =
  S.solve ctx

let solve_real () = raise (Failure "Undefined function solve_real()")

let fresh_int_var () =
  Db_logic.M.M_Var (Id'.gen_id Type.Y_Int)

let fresh_bool_var () =
  Formula.F_Atom
    (Db_logic.A.A_Bool
       (Db_logic.M.M_Var (Id'.gen_id Type.Y_Bool)))

let fresh_real_var () =  Db_logic.M.M_Var (Id'.gen_id Type.Y_Real)

let ideref = function
  | Db_logic.M.M_Var v ->
    S.deref_int ctx v
  | _ ->
    None

let bderef = function
  | Formula.F_Atom (Db_logic.A.A_Bool (Db_logic.M.M_Var v)) ->
    S.deref_bool ctx v
  | _ ->
    None

let rderef = function
  | Db_logic.M.M_Var v ->
    None
  | _ ->
    None

let toi x =
  Db_logic.M.M_Int (Core.Std.Int63.of_int x)

let gen_id = Id'.gen_id

let string_of_result =
  let open Terminology in
  function
  | R_Opt ->
    "opt"
  | R_Sat ->
    "sat"
  | R_Unbounded ->
    "unbounded"
  | R_Unsat ->
    "unsat"
  | R_Unknown ->
    "unknown"

let solve_print_result () =
  print_endline (string_of_result (solve ()))

let argv =
  if !Sys.interactive then
    Sys.argv
  else
    let open Core.Std.Array in
    slice Sys.argv 1 (length Sys.argv)
