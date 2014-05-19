open Core.Std
open Scip_idl
open Terminology
open Core.Int_replace_polymorphic_compare

exception Scip_Exn of (Here.t * retcode)

(* implementation first, then wrapping things up in modules and
   functors *)

type scip_ctx = {
  r_ctx: scip;
  r_var_d: var Dequeue.t;
  mutable r_cch: cch option;
  mutable r_constraints_n: int;
  mutable r_has_objective: bool;
  mutable r_sol: sol option;
  mutable r_cuts_n: int;
}

let dummy_f = ""

let dummy_var = cc_handler_zero_var ()

type var = Scip_idl.var

let compare_var x y =
  Int.compare (uintptr_t_of_var x) (uintptr_t_of_var y)

let hash_var = uintptr_t_of_var

let sexp_of_var v =
  Int.sexp_of_t (uintptr_t_of_var v)

let ivar_of_bvar x = x

(* TODO : check bounds *)
let bvar_of_ivar x = x

let rvar_of_ivar x = x 

type named_constraint = cons

let string_of_retcode = function
  |  SCIP_OKAY  ->
    "SCIP_OKAY"
  |  SCIP_ERROR  ->
    "SCIP_ERROR"
  |  SCIP_NOMEMORY  ->
    "SCIP_NOMEMORY"
  |  SCIP_READERROR  ->
    "SCIP_READERROR"
  |  SCIP_WRITEERROR  ->
    "SCIP_WRITEERROR"
  |  SCIP_NOFILE  ->
    "SCIP_NOFILE"
  |  SCIP_FILECREATEERROR  ->
    "SCIP_FILECREATEERROR"
  |  SCIP_LPERROR  ->
    "SCIP_LPERROR"
  |  SCIP_NOPROBLEM  ->
    "SCIP_NOPROBLEM"
  |  SCIP_INVALIDCALL  ->
    "SCIP_INVALIDCALL"
  |  SCIP_INVALIDDATA  ->
    "SCIP_INVALIDDATA"
  |  SCIP_INVALIDRESULT  ->
    "SCIP_INVALIDRESULT"
  |  SCIP_PLUGINNOTFOUND  ->
    "SCIP_PLUGINNOTFOUND"
  |  SCIP_PARAMETERUNKNOWN  ->
    "SCIP_PARAMETERUNKNOWN"
  |  SCIP_PARAMETERWRONGTYPE  ->
    "SCIP_PARAMETERWRONGTYPE"
  |  SCIP_PARAMETERWRONGVAL  ->
    "SCIP_PARAMETERWRONGVAL"
  |  SCIP_KEYALREADYEXISTING  ->
    "SCIP_KEYALREADYEXISTING"
  |  SCIP_MAXDEPTHLEVEL  ->
    "SCIP_MAXDEPTHLEVEL"

let ok_or_fail_of_retcode = function
  | SCIP_OKAY ->
    `Ok
  | _ ->
    `Fail

let assert_ok loc = function
  | SCIP_OKAY ->
    ()
  | v ->
    raise (Scip_Exn (loc, v))

let assert_ok1 loc = function
  | SCIP_OKAY, r ->
    r
  | v, _ ->
    raise (Scip_Exn (loc, v))

let assert_ok2 loc = function
  | SCIP_OKAY, r1, r2 ->
    r1, r2
  | v, r1, r2 ->
    raise (Scip_Exn (loc, v))

let string_of_version () =
  Printf.sprintf "%d.%d.%d"
    (sCIPmajorVersion ())
    (sCIPminorVersion ())
    (sCIPtechVersion ())

let config_list = [
  _here_,
  (fun c -> sCIPsetEmphasis c SCIP_PARAMEMPHASIS_EASYCIP true);
  _here_,
  (fun c -> sCIPsetIntParam c "display/verblevel" 0);
  _here_,
  (fun c -> sCIPsetPresolving c SCIP_PARAMSETTING_OFF true);
]

let run_config_list c =
  List.iter config_list ~f:(fun (h, f) -> assert_ok h (f c))

let make_ctx () =
  let r_ctx = assert_ok1 _here_ (sCIPcreate ()) in
  let r_cch = Some (new_cc_handler r_ctx None None) in
  cc_handler_include (Option.value_exn r_cch ~here:_here_);
  assert_ok _here_ (sCIPincludeDefaultPlugins r_ctx);
  assert_ok _here_ (sCIPcreateProbBasic r_ctx "prob");
  run_config_list r_ctx;
  let r_var_d = Dequeue.create () ~initial_length:1023
  and r_constraints_n = 0
  and r_has_objective = false
  and r_sol = None 
  and r_cuts_n = 0 in
  {r_ctx; r_cch; r_var_d; r_constraints_n; r_has_objective;
   r_sol; r_cuts_n}

let new_f _ id _ = id

let scip_lb_int {r_ctx} =
  Option.value_map
    ~default:(~-. (sCIPinfinity r_ctx))
    ~f:Int63.to_float

let scip_ub_int {r_ctx} =
  Option.value_map
    ~default:(sCIPinfinity r_ctx)
    ~f:Int63.to_float

let scip_lb_real {r_ctx} =
  Option.value
    ~default:(~-. (sCIPinfinity r_ctx))

let scip_ub_real {r_ctx} =
  Option.value 
    ~default:(sCIPinfinity r_ctx)

let new_ivar ({r_ctx; r_var_d} as r) t =
  let i = Dequeue.length r_var_d in
  let id = Printf.sprintf "v%d" i in
  let v =
    assert_ok1 _here_
      (match t with
      | T_Int (lb, ub) ->
        sCIPcreateVarBasic
          r_ctx id (scip_lb_int r lb) (scip_ub_int r ub)
          0. SCIP_VARTYPE_INTEGER
      | T_Real (lb, ub) ->
        sCIPcreateVarBasic
          r_ctx id (scip_lb_real r lb) (scip_ub_real r ub)
          0. SCIP_VARTYPE_CONTINUOUS) in
  assert_ok _here_ (sCIPaddVar r_ctx v);
  Dequeue.enqueue_back r_var_d v; v

let new_bvar {r_ctx; r_var_d} =
  let i = Dequeue.length r_var_d in
  let id = Printf.sprintf "v%d" i in
  let v =
    assert_ok1 _here_
      (sCIPcreateVarBasic r_ctx id 0.0 1.0 0. SCIP_VARTYPE_BINARY) in
  assert_ok _here_ (sCIPaddVar r_ctx v);
  Dequeue.enqueue_back r_var_d v; v

let new_ivar' ({r_ctx; r_var_d} as r) lb ub =
  let i = Dequeue.length r_var_d in
  let id = Printf.sprintf "v%d" i in
  let v =
    assert_ok1 _here_
      (sCIPcreateVarBasic
          r_ctx id (scip_lb_int r lb) (scip_ub_int r ub)
          0. SCIP_VARTYPE_INTEGER) in
  assert_ok _here_ (sCIPaddVar r_ctx v);
  Dequeue.enqueue_back r_var_d v;v

let new_rvar ({r_ctx; r_var_d} as r) lb ub =
   let i = Dequeue.length r_var_d in
  let id = Printf.sprintf "v%d" i in
  let v =
    assert_ok1 _here_ 
      ( sCIPcreateVarBasic
          r_ctx id (scip_lb_real r lb) (scip_ub_real r ub)
          0. SCIP_VARTYPE_CONTINUOUS ) in
  assert_ok _here_ (sCIPaddVar r_ctx v);
  Dequeue.enqueue_back r_var_d v;v

let negate_bvar {r_ctx; r_var_d} v =
  let v = assert_ok1 _here_ (sCIPgetNegatedVar r_ctx v) in
  Dequeue.enqueue_back r_var_d v; v

let iexpr_vars (l, o) =
  Array.of_list (List.map l ~f:snd)

let make_constraint_id ({r_constraints_n} as r) =
  let id = Printf.sprintf "c%d" r_constraints_n in
  r.r_constraints_n <- r_constraints_n + 1;
  id

let create_constraint ({r_ctx} as r) eq l o =
  assert_ok1 _here_
    (sCIPcreateConsBasicLinear r_ctx
       (make_constraint_id r)
       (Array.of_list_map ~f:snd l)
       (Array.of_list_map ~f:(Fn.compose Int63.to_float fst) l)
       (-.
           (if eq then
               Float.(neg o)
            else
               sCIPinfinity r_ctx))
        o)

let create_real_constraint ({r_ctx} as r) eq l o =
  assert_ok1 _here_
    (sCIPcreateConsBasicLinear r_ctx
       (make_constraint_id r)
       (Array.of_list_map ~f:(
	 fun x -> (match (snd x) with
	            | W_Int x -> x
		    | W_Real x -> x)) 
	l)
       (Array.of_list_map ~f:fst l)
       (-.
	   (if eq then 
	       Float.(neg o)
	    else 
	       sCIPinfinity r_ctx))
       Float.(o))

let add_eq ({r_ctx} as r) l o =
  let c = create_constraint r true l (Int63.to_float o) in
  assert_ok _here_ (sCIPaddCons r_ctx c)

let add_real_eq ({r_ctx} as r) l o = 
  let c =  create_real_constraint r true l o in
  assert_ok _here_ (sCIPaddCons r_ctx c)

let add_le ({r_ctx} as r) l o =
  let c = create_constraint r false l (Int63.to_float o) in
  assert_ok _here_ (sCIPaddCons r_ctx c)

let add_real_le ({r_ctx} as r) l o =
  let c = (match l with
            | LP_Int s -> create_constraint r false s o
	    | LP_Mix s -> create_real_constraint r false s o) in
  assert_ok _here_ (sCIPaddCons r_ctx c)

let var_of_var_signed {r_ctx} = function
  | S_Pos v ->
    v
  | S_Neg v ->
    assert_ok1 _here_ (sCIPgetNegatedVar r_ctx v)

let add_indicator ({r_ctx} as r) v l o =
  let c =
    assert_ok1 _here_
      (sCIPcreateConsBasicIndicator r_ctx
         (make_constraint_id r)
         (var_of_var_signed r v)
         (Array.of_list_map ~f:snd l)
         (Array.of_list_map ~f:(Fn.compose Int63.to_float fst) l)
         (Int63.to_float o)) in
  assert_ok _here_ (sCIPaddCons r_ctx c)

let add_real_indicator ({r_ctx} as r) v l o =
  let variables, coeffs = match l with
    | LP_Int s -> 
      Array.of_list_map ~f:snd s, 
      Array.of_list_map ~f:(Fn.compose Int63.to_float fst) s
    | LP_Mix s -> 
      Array.of_list_map ~f:(fun x ->
	(match (snd x) with
	  | W_Int c -> c
	  | W_Real c -> c)) s,
      Array.of_list_map ~f:fst s in
  let c =
    assert_ok1 _here_
      (sCIPcreateConsBasicIndicator r_ctx
	 (make_constraint_id r)
	 (var_of_var_signed r v)
	 (variables)
	 (coeffs)
	 o) in
  assert_ok _here_ (sCIPaddCons r_ctx c)

let add_clause ({r_ctx; r_constraints_n} as r) l =
  let c =
    assert_ok1 _here_
      (let l =
         Array.of_list_map l
           ~f:(function
           | S_Pos v ->
             v
           | S_Neg v ->
             assert_ok1 _here_ (sCIPgetNegatedVar r_ctx v)) in
       sCIPcreateConsBasicLogicor r_ctx (make_constraint_id r) l) in
  assert_ok _here_ (sCIPaddCons r_ctx c)

let var_of_var_option {r_cch} =
  Option.value ~default:dummy_var

let add_call ({r_cch} as r) (v, o) f l =
  Scip_idl.cc_handler_call (Option.value_exn r_cch ~here:_here_)
    (var_of_var_option r v) (Int63.to_int64 o) f
    (Array.of_list_map l ~f:(Fn.compose (var_of_var_option r) fst))
    (Array.of_list_map l ~f:(Fn.compose Int63.to_int64 snd))

let add_objective {r_ctx; r_has_objective} l =
  if r_has_objective then
    `Duplicate
  else
    (List.iter l
       ~f:(fun (c, v) ->
         let c = Int63.to_float c in
         assert_ok _here_ (sCIPchgVarObj r_ctx v c));
     `Ok)

let add_real_objective {r_ctx; r_has_objective} l =
  if r_has_objective then
    `Duplicate
  else match l with
        | LP_Int s -> (List.iter s
                        ~f:(fun (c, v) ->
                             let c = Int63.to_float c in
                             assert_ok _here_ (sCIPchgVarObj r_ctx v c));
                      `Ok)
	| LP_Mix s ->  (List.iter s
			  ~f:(fun (c, v) ->
			    let x = (match v with | W_Int x -> x | W_Real x -> x) in
			    assert_ok _here_ (sCIPchgVarObj r_ctx x c));
			`Ok)

let result_of_status = function
  | SCIP_STATUS_OPTIMAL ->
    R_Opt
  | SCIP_STATUS_UNBOUNDED ->
    R_Unbounded
  | SCIP_STATUS_INFEASIBLE ->
    R_Unsat
  | _ ->
    R_Unknown

let sresult_of_response = function
  | N_Ok -> SCIP_DIDNOTFIND
  | N_Unsat -> SCIP_CUTOFF
  | N_Tightened -> SCIP_REDUCEDDOM

let write_ctx {r_ctx} filename =
  assert_ok _here_ (sCIPwriteOrigProblem r_ctx filename "lp" false)

let solve ({r_ctx; r_cch} as r) =
  cc_handler_finalize (Option.value_exn r_cch ~here:_here_);
  assert_ok _here_ (sCIPsolve r_ctx);
  let rval = result_of_status (sCIPgetStatus r_ctx) in
  (match rval with
  | R_Opt | R_Unbounded | R_Sat ->
    r.r_sol <- Some (sCIPgetBestSol r_ctx)
  | _ -> ());
  rval

let ideref_sol {r_ctx} sol v =
  let x = sCIPgetSolVal r_ctx sol v in
  let i = Int63.of_float x in
  if Float.(x > Int63.to_float i + 0.5) then
    Int63.succ i
  else
    i

let bderef_sol {r_ctx} sol v =
  Float.(>) (sCIPgetSolVal r_ctx sol v) 0.5

let rderef_sol {r_ctx} sol v = 
  (sCIPgetSolVal r_ctx sol v)

let ideref ({r_sol} as r) v =
  Option.map r_sol ~f:(fun s -> ideref_sol r s v)

let bderef ({r_sol} as r) v =
  Option.map r_sol ~f:(fun s -> bderef_sol r s v)

let rderef ({r_sol} as r) v = 
  Option.map r_sol ~f:(fun s -> rderef_sol r s v)

let branch {r_ctx} v x =
  let lb = sCIPvarGetLbLocal v
  and ub = sCIPvarGetUbLocal v in
  if Float.(lb < ub && lb <= x && ub >= x) then
    let r, _, _, _ = sCIPbranchVarVal r_ctx v x in
    ok_or_fail_of_retcode r
  else
    `Fail

let variables_number {r_var_d} = Dequeue.length r_var_d

let constraints_number {r_constraints_n} = r_constraints_n

let make_cut_id ({r_cuts_n} as r) =
  let id = Printf.sprintf "c%d" r_cuts_n in
  r.r_cuts_n <- r_cuts_n + 1;
  id

let add_cut_local ({r_ctx} as r) (l, o) =
  let row =
    assert_ok1 _here_
      (sCIPcreateEmptyRowCons r_ctx
         (sCIPfindConshdlr r_ctx "cc")
         (make_cut_id r)
         (-. (sCIPinfinity r_ctx)) (Int63.to_float o)
         true false false) in
  assert_ok _here_ (sCIPcacheRowExtensions r_ctx row);
  assert (not (List.is_empty l));
  List.iter l
    ~f:(fun (c, v) ->
      assert_ok _here_
        (sCIPaddVarToRow r_ctx row v (Int63.to_float c)));
  assert_ok _here_ (sCIPflushRowExtensions r_ctx row) ;
  assert_ok _here_ (sCIPaddCut r_ctx (scip_null_sol ()) row true)

let add_real_cut_local ({r_ctx} as r) (l, o) =
  let row =
    assert_ok1 _here_
      (sCIPcreateEmptyRowCons r_ctx
         (sCIPfindConshdlr r_ctx "cc")
         (make_cut_id r)
         (-. (sCIPinfinity r_ctx)) o
         true false false) in
  assert_ok _here_ (sCIPcacheRowExtensions r_ctx row);
  assert (not (List.is_empty l));
  List.iter l
    ~f:(fun (c, v) ->
      assert_ok _here_
        (sCIPaddVarToRow r_ctx row v c));
  assert_ok _here_ (sCIPflushRowExtensions r_ctx row) ;
  assert_ok _here_ (sCIPaddCut r_ctx (scip_null_sol ()) row true)

(* FIXME : do we really need the Option? *)

let name_diff {r_cch} v1 v2 =
  Option.(r_cch >>| fun r_cch -> cc_handler_add_dvar r_cch v1 v2)

module Types = struct
  type ctx = scip_ctx
  type ivar = var
  type bvar = var
  type rvar = var
  let compare_ivar = compare_var
  let hash_ivar = hash_var
  let sexp_of_ivar = sexp_of_var
  let compare_bvar = compare_var
  let hash_bvar = hash_var
  let sexp_of_bvar = sexp_of_var
  let compare_rvar = compare_var
  let hash_rvar = hash_var
  let sexp_of_rvar = sexp_of_var
  let ivar_of_bvar = ivar_of_bvar
  let bvar_of_ivar = bvar_of_ivar
  let rvar_of_ivar = rvar_of_ivar
end

module Types_uf = struct
  type f = string
  let compare_f = String.compare
  let hash_f = String.hash
  let sexp_of_f = String.sexp_of_t
  let dummy_f = dummy_f
end

module Access = struct
  let new_f = new_f
  let new_ivar = new_ivar
  let new_ivar' = new_ivar'
  let new_bvar = new_bvar
  let new_rvar = new_rvar
  let negate_bvar = negate_bvar
  let add_eq = add_eq
  let add_real_eq = add_real_eq
  let add_le = add_le
  let add_real_le = add_real_le
  let add_indicator = add_indicator
  let add_real_indicator = add_real_indicator
  let add_clause = add_clause
  let add_call = add_call
  let add_objective = add_objective
  let add_real_objective = add_real_objective
  let solve = solve
  let ideref = ideref
  let bderef = bderef
  let rderef = rderef 
  let write_ctx = write_ctx
  let name_diff = name_diff
end

module Dp_access_bounds = struct

  include Types

  type sol' = sol

  type sol = sol'

  let get_lb_local {r_ctx} v =
    let lb = sCIPvarGetLbLocal v in
    if sCIPisEQ r_ctx lb (-. (sCIPinfinity r_ctx)) then
      None
    else
      Some (Int63.of_float lb)

  let get_real_lb_local {r_ctx} v = 
    let lb = sCIPvarGetLbLocal v in
    if sCIPisEQ r_ctx lb (-. (sCIPinfinity r_ctx)) then
      None
    else
      (Some lb)

  let get_ub_local {r_ctx} v =
    let ub = sCIPvarGetUbLocal v in
    if sCIPisEQ r_ctx ub (sCIPinfinity r_ctx) then
      None
    else
      Some (Int63.of_float ub)

  let get_real_ub_local {r_ctx} v = 
    let ub = sCIPvarGetUbLocal v in
    if sCIPisEQ r_ctx ub (-. (sCIPinfinity r_ctx)) then
      None
    else
      (Some ub)

  let bderef_local r v =
    Option.(get_lb_local r v >>| Int63.((<=) one))

  let set_lb_local {r_ctx} v x =
    let infeasible, tightened =
      let cons = scip_null_cons ()
      and x = Int63.to_float x in
      assert_ok2 _here_ (sCIPinferVarLbCons r_ctx v x cons 0 true) in
    if infeasible then
      `Infeasible
    else if tightened then
      `Tightened
    else
      `Ok

let set_real_lb_local {r_ctx} v x =
    let infeasible, tightened =
      let cons = scip_null_cons () in
      assert_ok2 _here_ (sCIPinferVarLbCons r_ctx v x cons 0 true) in
    if infeasible then
      `Infeasible
    else if tightened then
      `Tightened
    else
      `Ok

  let set_ub_local {r_ctx} v x =
    let infeasible, tightened =
      let cons = scip_null_cons ()
      and x = Int63.to_float x in
      assert_ok2 _here_ (sCIPinferVarUbCons r_ctx v x cons 0 true) in
    if infeasible then
      `Infeasible
    else if tightened then
      `Tightened
    else
      `Ok

 let set_real_ub_local {r_ctx} v x =
    let infeasible, tightened =
      let cons = scip_null_cons () in
      assert_ok2 _here_ (sCIPinferVarUbCons r_ctx v x cons 0 true) in
    if infeasible then
      `Infeasible
    else if tightened then
      `Tightened
    else
      `Ok

  let ideref_sol = ideref_sol

  let bderef_sol = bderef_sol

  let rderef_sol = rderef_sol

end

module Dp_access = struct

  include Dp_access_bounds

  let ibranch = branch

  let rbranch = branch

  let ibranch_nary {r_ctx} v ~middle ~n ~width =
    let r, n = sCIPbranchVarValNary r_ctx v middle n width 1. in
    match r with
    | SCIP_OKAY ->
      if n > 0 then
        `Ok
      else
        raise (Scip_Exn (_here_, SCIP_OKAY))
    | _ ->
      `Fail

  let rbranch_nary = ibranch_nary


  let bbranch r v = branch r v 0.5

end

module Dvars =
  Dvars.Make (struct
    include Dp_access_bounds
    let name_diff = name_diff
  end)

module Drvars =
  Drvars.Make (struct
    include Dp_access_bounds
    let name_real_diff = name_diff
  end)

module Cut_gen_access = struct

  include Dp_access_bounds

  module Dvars = Dvars

  module Drvars = Drvars

  (* type dvar = Dvars.t *)

  let add_cut_local = add_cut_local

  let add_real_cut_local = add_real_cut_local

  let rderef_sol = rderef_sol

end

module Scip_basic : Imt_intf.S_unit_creatable = struct
  include Types
  include Types_uf
  include Access
  let make_ctx = make_ctx
end

module Scip_with_dp = struct

  include Types
  include Types_uf

  module F

    (D : Imt_intf.S_dp
     with type ivar_plug := ivar
     and type bvar_plug := bvar
     and type rvar_plug := rvar) =

  struct

    module D' = D.F(Dp_access)

    include Types
    include Types_uf
    include Access

    let make_dp d_ctx ctx =
      make_dP (object
        method push_level =
          D'.push_level d_ctx ctx
        method backtrack =
          D'.backtrack d_ctx ctx
        method propagate =
          sresult_of_response (D'.propagate d_ctx ctx)
        method check =
          D'.check d_ctx ctx
        method branch =
          match D'.branch d_ctx ctx with
          | `Ok ->
            true
          | `Fail ->
            false
      end)

    let make_ctx d =
      let r_ctx = assert_ok1 _here_ (sCIPcreate ())
      and r_cch = None
      and r_var_d = Dequeue.create ()
      and r_constraints_n = 0
      and r_has_objective = false
      and r_sol = None
      and r_cuts_n = 0 in
      let rval = {
        r_ctx;
        r_cch;
        r_var_d;
        r_constraints_n;
        r_has_objective;
        r_sol;
        r_cuts_n
      } in
      let o = Some (make_dp d rval) in
      (*let o = None in *)
      let r_cch = Some (new_cc_handler r_ctx o None) in
      rval.r_cch <- r_cch;
      cc_handler_include (Option.value_exn rval.r_cch ~here:_here_);
      assert_ok _here_ (sCIPincludeDefaultPlugins r_ctx);
      assert_ok _here_ (sCIPcreateProbBasic r_ctx "prob");
      run_config_list r_ctx;
      rval
    
    let register_var {r_cch} v =
      let r_cch = Option.value_exn ~here:_here_ r_cch in
      cc_handler_catch_var_events r_cch v

    let register_ivar = register_var

    let register_bvar = register_var

    let register_rvar = register_var

  end

end

module Scip_with_cut_gen = struct

  include Types
  include Types_uf
    
  type sol' = sol
    
  type sol = sol'

  module Dvars = Dvars

  module Drvars = Drvars

  module F

    (D : Imt_intf.S_cut_gen
     with type ivar_plug := ivar
     and type bvar_plug := bvar
     and type rvar_plug := rvar
     and type dvar_int_plug := Dvars.t
     and type dvar_real_plug := Drvars.t) =

  struct

    module D' = D.F(Cut_gen_access)

    include Types
    include Types_uf
    include Access

    let register_var {r_cch} v =
      let r_cch = Option.value_exn ~here:_here_ r_cch in
      cc_handler_catch_var_events r_cch v

    let register_ivar = register_var

    let register_bvar = register_var

    let register_rvar = register_var

    let make_cut_gen d_ctx ctx =
      make_cut_Gen (object
        method push_level =
          D'.push_level d_ctx ctx
        method backtrack =
          D'.backtrack d_ctx ctx
        method generate =
          match D'.generate d_ctx ctx (scip_null_sol ()) with
          | `Unknown ->
            SCIP_DIDNOTFIND
          | `Sat ->
            SCIP_FEASIBLE
          | `Unsat_Cut_Gen ->
            SCIP_SEPARATED
          | `Cutoff ->
            SCIP_CUTOFF
        method check =
          D'.check d_ctx ctx
      end)

    let make_ctx c =
      let r_ctx = assert_ok1 _here_ (sCIPcreate ())
      and r_cch = None
      and r_var_d = Dequeue.create ()
      and r_constraints_n = 0
      and r_has_objective = false
      and r_sol = None
      and r_cuts_n = 0 in
      let rval = {
        r_ctx;
        r_cch;
        r_var_d;
        r_constraints_n;
        r_has_objective;
        r_sol;
        r_cuts_n
      } in
      let o = Some (make_cut_gen c rval) in
      let r_cch = Some (new_cc_handler r_ctx None o) in
      rval.r_cch <- r_cch;
      cc_handler_include (Option.value_exn rval.r_cch ~here:_here_);
      assert_ok _here_ (sCIPincludeDefaultPlugins r_ctx);
      assert_ok _here_ (sCIPcreateProbBasic r_ctx "prob");
      run_config_list r_ctx;
      rval

    let create_dvar = Dvars.create_dvar

    let create_real_dvar = Drvars.create_real_dvar
    
  end

end
