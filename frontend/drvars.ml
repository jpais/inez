open Core.Std
open Terminology

module Make

  (S : sig

    include Imt_intf.S_rvar

    include Imt_intf.S_real_bounds with type t := rvar

    val name_real_diff : ctx -> rvar -> rvar -> Float.t -> rvar option

  end) =

struct
  type ctx = S.ctx

  type sol = S.sol

  type t = 
      S.rvar signed option roffset *
	S.rvar option roffset *
	S.rvar option roffset       
  with compare, sexp_of    

  let compare = compare_t

  let hashable = {
    Hashtbl.Hashable.
    compare = compare;
    hash = Hashtbl.hash;
    sexp_of_t = sexp_of_t
  }

  let create_drvar_base r v1 v2 o =
    match v1, v2 with
    | Some v1, None ->
      Some (S_Pos v1)
    | None, Some v2 ->
      Some (S_Neg v2)
    | None, None ->
      None
    | Some v1, Some v2 when S.compare_rvar v1 v2 > 0 ->
      Option.(S.name_real_diff r v1 v2 o >>| (fun v -> S_Pos v))
    | Some v1, Some v2 when S.compare_rvar v1 v2 < 0 ->
      Option.(S.name_real_diff r v2 v1 o >>| (fun v -> S_Neg v))
    | Some v1, Some v2 ->
      None

  let create_drvar r (v1, o1 as ov1) (v2, o2 as ov2) =
    let o = Float.(o1 - o2) in
    (create_drvar_base r v1 v2 Float.(-.o), o), ov1, ov2

  let get_lb_local_base r = function
    | Some (S_Pos v) ->
      S.get_real_lb_local r v
    | Some (S_Neg v) ->
      Option.( (S.get_real_ub_local r v) >>| Float.(neg) )
    | None ->
      Some Float.zero

  let get_ub_local_base r = function
    | Some (S_Pos v) ->
      S.get_real_ub_local r v
    | Some (S_Neg v) ->
      Option.(S.get_real_lb_local r v >>| Float.(neg))
    | None ->
      Some Float.zero

  let ideref_sol_base r sol = function
    | Some (S_Pos v) ->
      S.rderef_sol r sol v
    | Some (S_Neg v) ->
      Float.(-. S.rderef_sol r sol v)
    | None ->
      Float.zero

  let set_lb_local_base r v x =
    match v with
    | Some (S_Pos v) ->
      S.set_real_lb_local r v x
    | Some (S_Neg v) ->
      S.set_real_ub_local r v Float.(-. x)
    | None when Float.(x <=. zero) ->
      `Ok
    | None ->
      `Infeasible

  let set_ub_local_base r v x =
    match v with
    | Some (S_Pos v) ->
      S.set_real_ub_local r v x
    | Some (S_Neg v) ->
      S.set_real_lb_local r v Float.(-. x)
    | None when Float.(x >=. zero) ->
      `Ok
    | None ->
      `Infeasible

  let get_real_lb_local r ((dv, o), _, _) =
    Option.(get_lb_local_base r dv >>| Float.(+) o)

  let get_real_ub_local r ((dv, o), _, _) =
    Option.(get_ub_local_base r dv >>| Float.(+) o)

  let rderef_sol r sol ((dv, o), _, _) =
    Float.(ideref_sol_base r sol dv + o)

  let set_real_lb_local r ((dv, o), _, _) x =
    set_lb_local_base r dv Float.(x - o)

  let set_real_ub_local r ((dv, o), _, _) x =
    set_ub_local_base r dv Float.(x - o)

  let get_left _ (_, ov, _) = ov

  let get_right _ (_, _, ov) = ov

end
