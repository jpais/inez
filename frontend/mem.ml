open Core.Std
open Terminology
open Bounds

let dbg = true

module Zom = struct

  type 'a t = Z0 | Z1 of 'a | Zn of int

  let update z x ~equal =
    match z with
    | Z0 ->
      Z1 x
    | Z1 x' when equal x x' ->
      z
    | Z1 _ ->
      Zn 2
    | Zn n ->
      Zn (n + 1)

end

let dequeue_exists_with_swap d ~f =
  let rec g i n = 
    if i <= n then
      let a = Dequeue.get_opt d i in
      let a = Option.value_exn a ~here:_here_ in
      if f a then
        true
      else
        (Dequeue.drop_front d;
         Dequeue.enqueue_back d a;
         g (i + 1) n)
    else
      false in
  match Dequeue.front_index d, Dequeue.back_index d with
  | Some i, Some n ->
    g i n
  | _, _ ->
    false

let array_foldi_responses a ~f =
  let n = Array.length a in
  let rec g i acc =
    if i >= n then
      acc
    else
      match f i a.(i) with
      | N_Unsat ->
        N_Unsat
      | N_Tightened ->
        g (i + 1) N_Tightened
      | N_Ok ->
        g (i + 1) acc in
  g 0 N_Ok

let dequeue_fold_responses d ~f =
  Dequeue.fold d ~init:N_Ok
    ~f:(fun acc x ->
      match acc with
      | N_Unsat ->
        N_Unsat
      | _ ->
        match f x with
        | N_Ok ->
          acc
        | r ->
          r)

let intercept_response s r =
  if dbg then
    (let s2 = Sexplib.Conv.string_of_sexp (sexp_of_response r) in
     Printf.printf "%s: %s\n%!" s s2);
  r

let intercept_bool s b =
  if dbg then Printf.printf "%s: %b\n%!" s b;
  b

let intercept_ok_or_fail s a =
  if dbg then
    (let s2 = match a with `Ok -> "`Ok" | `Fail -> "`Fail" in
     Printf.printf "%s: %s\n%!" s s2);
  a

let bool_of_ok_or_fail = function
  | `Ok   -> true
  | `Fail -> false

let ok_for_true = function
  | true  -> `Ok
  | false -> `Fail

module Make (Imt : Imt_intf.S_essentials) = struct

  let hashable_bvar = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = Imt.compare_bvar;
    sexp_of_t = Imt.sexp_of_bvar
  }

(** Pure Int DB*)

  type row = Imt.ivar option offset array
  with compare, sexp_of

  type db = row list
  with compare, sexp_of

  let hashable_db = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_db;
    sexp_of_t = sexp_of_db
  }

  type idiff = Imt.ivar * Imt.ivar
  with compare, sexp_of

  let hashable_idiff = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_idiff;
    sexp_of_t = sexp_of_idiff
  }

  type row_map = row list Int63.Map.t
  with compare, sexp_of

  type index = row_map * row_map * row list
  with compare, sexp_of

  type occ = row * index * int * int option ref
  with compare, sexp_of

  type bounds_array = (Int63.t option * Int63.t option) array
  with compare, sexp_of

  type mbounds_key = bounds_array * row_map
  with compare, sexp_of

  let hashable_mbounds_key = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_mbounds_key;
    sexp_of_t = sexp_of_mbounds_key
  }

  type mbounds_value =
    bounds_array * row Zom.t * bool


(** Mixed Int/Real DB *)

(** Represents a row of a DB table. The row is an array of ivars and rvars*)
  type mvar = (Imt.ivar, Imt.rvar) Terminology.ireither
  with compare, sexp_of

  type mvar_bound = (Int63.t option, Float.t option) ireither
  with compare, sexp_of 

  (* type mixed_row = (Imt.ivar option, Imt.rvar option) ireither roffset array
  with compare, sexp_of
  *)

type mixed_row = (Imt.ivar option offset, Imt.rvar option roffset) ireither array
  with compare, sexp_of


(** Represents a table*)
  type mixed_db = mixed_row list
  with compare, sexp_of

  let hashable_mixed_db = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_mixed_db;
    sexp_of_t = sexp_of_mixed_db
  }

(** A variable that represents the difference between 2 ivars or 2 rvars
  type mixed_diff = (Imt.ivar * Imt.ivar, Imt.rvar * Imt.rvar) Terminology.ireither 
  with compare, sexp_of
*)
  type mixed_diff = (mvar * mvar)
  with compare, sexp_of

  let hashable_mixed_diff = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_mixed_diff;
    sexp_of_t = sexp_of_mixed_diff
  }

(** Index over the table. Each i represents a list of mixed rows whose first column element i *)
  type mixed_row_map = mixed_row list Float.Map.t
  with compare, sexp_of

(** Represents a partition of the table as follows:
- the first map consists of rows that only have constants (no variables)
- second map consists of rows whose first element is a constant but have a variable somewhere
- list of rows that begin with a variable*)
  type mixed_index = mixed_row_map * mixed_row_map * mixed_row list
  with compare, sexp_of

(** Represents the constrains:
- First row is the symbolic row whose membership we are testing.
- The index represents the table where we are testing the membership.
- int represents the column of the table that is being indexed (default 0).
- int option ref: if not None, then the constrain is satisfied at level n of the search tree. The objective is to stop branching and propagation.*)
  type mixed_occ = mixed_row * mixed_index * int * int option ref
  with compare, sexp_of

(*  type mixed_bounds_array = ((Int63.t,Float.t) ireither option * (Int63.t,Float.t) ireither option) array
  with compare, sexp_of
*)

  type mixed_bounds_array = (mvar_bound * mvar_bound) array
  with compare, sexp_of

(** Bounds for a constant only partition of the table*)
  type mixed_bounds_key = mixed_bounds_array * mixed_row_map
  with compare, sexp_of

   let hashable_mixed_bounds_key = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_mixed_bounds_key;
    sexp_of_t = sexp_of_mixed_bounds_key
  }

(** Symbolic expression * number of candidates * true iff already has an equal candidate*)
  type mixed_bounds_value = mixed_bounds_array * mixed_row Zom.t * bool


  type stats = {
    mutable s_propagate     :  int;
    mutable s_check         :  int;
    mutable s_branch        :  int;
    mutable s_push_level    :  int;
    mutable s_backtrack     :  int;
    mutable s_mbounds_fail  :  int;
    mutable s_mbounds_all   :  int;
    mutable s_maxdepth      :  int;
  } with sexp_of

  type ctx = {
    r_idb_h          :  (db, index) Hashtbl.t;
    r_mdb_h          :  (mixed_db, mixed_index) Hashtbl.t;
    r_bvar_d         :  Imt.bvar Dequeue.t;
    r_diff_h         :  (idiff, Imt.ivar) Hashtbl.t;
    r_mdiff_h        :  (mixed_diff, (Imt.ivar, Imt.rvar) Terminology.ireither) Hashtbl.t;
    r_occ_h          :  (Imt.bvar, occ Dequeue.t) Hashtbl.t;
    r_mocc_h         :  (Imt.bvar, mixed_occ Dequeue.t) Hashtbl.t;
    r_mbounds_h      :  (mbounds_key, mbounds_value) Hashtbl.t;
    r_mixbounds_h    :  (mixed_bounds_key, mixed_bounds_value) Hashtbl.t;
    r_stats          :  stats;
    mutable r_level  :  int;
    mutable r_ismixed:  bool;
  }

  let make_ctx () = {
    r_idb_h =
      Hashtbl.create () ~size:64 ~hashable:hashable_db;
    r_mdb_h =
      Hashtbl.create () ~size:64 ~hashable:hashable_mixed_db;
    r_bvar_d =
      Dequeue.create () ~initial_length:31;
    r_diff_h =
      Hashtbl.create () ~size:1024 ~hashable:hashable_idiff;
    r_mdiff_h = 
      Hashtbl.create () ~size:1024 ~hashable:hashable_mixed_diff;
    r_occ_h =
      Hashtbl.create () ~size:1024 ~hashable:hashable_bvar;
    r_mocc_h =
      Hashtbl.create () ~size:1024 ~hashable:hashable_bvar;
    r_mbounds_h =
      Hashtbl.create () ~size:255 ~hashable:hashable_mbounds_key;
    r_mixbounds_h =
      Hashtbl.create () ~size:255 ~hashable:hashable_mixed_bounds_key;
    r_stats = {
      s_propagate = 0;
      s_check = 0;
      s_branch = 0;
      s_push_level = 0;
      s_backtrack = 0;
      s_mbounds_fail = 0;
      s_mbounds_all = 0;
      s_maxdepth = 0;
    };
    r_level = 0;
    r_ismixed = false;
  }

  let print_stats {r_stats} =
    Sexplib.Sexp.output_hum stdout (sexp_of_stats r_stats);
    print_newline ()

  let all_concrete =
    Array.for_all ~f:(function None, _ -> true | _ -> false)

  let all_concrete_mixed = 
    Array.for_all ~f:(function
                       | W_Int (None, _) | W_Real (None, _) -> true
		       | _ -> false)

let index_of_db_dimension l i =
    List.fold_left l
      ~init:(Int63.Map.empty, Int63.Map.empty, [])
      ~f:(fun (accm1, accm2, accl) data ->
        match Array.get data i with
        | None, key when all_concrete data ->
          Map.add_multi accm1 ~key ~data, accm2, accl
        | None, key ->
          accm1, Map.add_multi accm2 ~key ~data, accl
        | _ ->
          accm1, accm2, data :: accl)


  let index_of_mixed_db_dimension l i =
    List.fold_left l
      ~init:(Float.Map.empty, Float.Map.empty, [])
      ~f:(fun (accm1, accm2, accl) data ->
        match Array.get data i with
	  | W_Int (None, key) when all_concrete_mixed data ->
	    let key = Int63.to_float key in
            Map.add_multi accm1 ~key ~data, accm2, accl
	  | W_Real (None, key) when all_concrete_mixed data ->
	    Map.add_multi accm1 ~key ~data, accm2, accl
          | W_Int  (None, key) ->
	    let key = Int63.to_float key in
            accm1, Map.add_multi accm2 ~key ~data, accl
	  | W_Real (None, key) ->
	    accm1, Map.add_multi accm2 ~key ~data, accl
          | _ ->
            accm1, accm2, data :: accl)


  let index_of_db {r_idb_h} d i =
    let default () = index_of_db_dimension d i in
    Hashtbl.find_or_add r_idb_h d ~default

  let index_of_mdb {r_mdb_h} d i =
    let default () = index_of_mixed_db_dimension d i in
    Hashtbl.find_or_add r_mdb_h d ~default

  let bvar_in_dequeue d v =
    let f x = Imt.compare_bvar x v = 0 in
    Dequeue.exists d ~f

  let rec ivar_of_diff ({r_diff_h} as r) v1 v2 ~fd ~frv =
    if Imt.compare_ivar v1 v2 > 0 then
      ivar_of_diff r v2 v1 ~fd ~frv
    else if Imt.compare_ivar v1 v2 = 0 then
      None
    else
      let default () =
        assert (Imt.compare_ivar v1 v2 < 0);
        fd v1 v2 in
      Some (Hashtbl.find_or_add r_diff_h (v1, v2) ~default)

  let rec var_of_mdiff ({r_mdiff_h} as r) v1 v2 ~fd ~frv =
    match v1, v2 with
      | W_Int x, W_Int y ->
	if Imt.compare_ivar x y > 0 then
	  var_of_mdiff r v2 v1 ~fd ~frv
	else if Imt.compare_ivar x y = 0 then
	  None
	else
	  let default () =
            assert (Imt.compare_ivar x y < 0);
            ((fd v1 v2)) in
	  Some (Hashtbl.find_or_add r_mdiff_h (v1, v2) ~default)
      | W_Real x, W_Real y ->
	if Imt.compare_rvar x y > 0 then
	  var_of_mdiff r v2 v1 ~fd ~frv
	else if Imt.compare_rvar x y = 0 then
	  None
	else let default () = 
	   assert (Imt.compare_rvar x y < 0);
	   ((fd v1 v2)) in
	 Some (Hashtbl.find_or_add r_mdiff_h (v1, v2) ~default)
      | _, _ -> None
      

  let register_diffs r row1 row2 ~fd ~frv =
    Array.iter2_exn row1 row2
      ~f:(fun (v1, _) (v2, _) ->
        match v1, v2 with
        | Some v1, Some v2 when not (Imt.compare_ivar v1 v2 = 0) ->
          let v = ivar_of_diff r v1 v2 ~fd ~frv in
          let v = Option.value_exn v ~here:_here_ in
          frv v
        | Some v, _ | _, Some v ->
          frv v
        | None, None ->
          ())

  let register_mdiffs r 
      (row1: mixed_row) 
      (row2: mixed_row) ~fd ~frv = 
    Array.iter2_exn row1 row2
      ~f:(fun v1 v2 ->
	match v1, v2 with
	  | W_Int (Some x1, _), W_Int (Some x2, _) when not (Imt.compare_ivar x1 x2 = 0) ->
	    let v = var_of_mdiff r (W_Int x1) (W_Int x2) ~fd ~frv in
	    let v = Option.value_exn v ~here:_here_ in
	    frv v
	  | W_Real (Some x1, _), W_Real (Some x2, _) when not (Imt.compare_rvar x1 x2 = 0) ->
	    let v = var_of_mdiff r (W_Real x1) (W_Real x2) ~fd ~frv in
	    let v = Option.value_exn v ~here:_here_ in
	    frv v
	  | W_Int _, W_Real _ | W_Real _ , W_Int _ -> raise (Failure "Unexpected case register_mdiffs")
	  | W_Int (Some v, _), _ | _, W_Int (Some v, _) ->
	    frv (W_Int v)
	  | W_Real (Some v, _), _ | _, W_Real (Some v, _) ->
            frv (W_Real v)
	  | W_Int (None, _), W_Int (None, _) -> ()
	  | W_Real (None,_), W_Real (None,_) -> ()
      )

  let assert_membership
      ({r_bvar_d; r_occ_h} as r) b e l ~fd ~frv =
    let e = Array.of_list e
    and l = List.map l ~f:Array.of_list in
    List.iter l ~f:(register_diffs r e ~fd ~frv);
    let index = index_of_db r l 0 in
    if not (bvar_in_dequeue r_bvar_d b) then
      Dequeue.enqueue_front r_bvar_d b;
    let occ = e, index, 0, ref None in
    let d =
      let initial_length = 64 and never_shrink = false in
      let default = Dequeue.create ~initial_length ~never_shrink in
      Hashtbl.find_or_add r_occ_h b ~default in
    Dequeue.enqueue_front d occ

  let assert_mixed_membership
      ({r_bvar_d; r_mocc_h} as r) b e l ~fd ~frv =
    let e = Array.of_list e
    and l = List.map l ~f:Array.of_list in
    List.iter l ~f:(register_mdiffs r e ~fd ~frv);
    r.r_ismixed <- true;
    let index = index_of_mdb r l 0 in
    if not (bvar_in_dequeue r_bvar_d b) then
      Dequeue.enqueue_front r_bvar_d b;
    let mocc = e, index, 0, ref None in
    let d =
      let initial_length = 64 and never_shrink = false in
      let default = Dequeue.create ~initial_length ~never_shrink in
      Hashtbl.find_or_add r_mocc_h b ~default in
    Dequeue.enqueue_front d mocc

  module F

    (S : Imt_intf.S_dp_access
     with type ivar := Imt.ivar
     and type bvar := Imt.bvar
     and type rvar := Imt.rvar) =

  struct

    type 'a folded = row -> bounds:bounds_array -> acc:'a -> 'a

    type 'a folded_no_bounds = row -> acc:'a -> 'a

    type 'a mapped = row -> bounds:bounds_array -> 'a

(** Mixed types *)
    type 'a mixed_folded = mixed_row -> bounds:mixed_bounds_array -> acc:'a -> 'a

    type 'a mixed_folded_no_bounds = mixed_row -> acc:'a -> 'a

    type 'a mixed_mapped = mixed_row -> bounds:mixed_bounds_array -> 'a

    let lb_of_ovar r' = function
      | Some v, o ->
        Option.(S.get_lb_local r' v >>| Int63.(+) o)
      | None, o ->
        Some o

    let ub_of_ovar r' = function
      | Some v, o ->
        Option.(S.get_ub_local r' v >>| Int63.(+) o)
      | None, o ->
        Some o


let lb_of_movar r' = function
      | W_Real (Some v, o) -> 
	(match (S.get_real_lb_local r' v) with
          | Some x -> W_Real (Some (Float.(x + o)))
          | _ -> W_Real None)
      | W_Int (Some v, o) -> 
	(match (S.get_lb_local r' v) with
	  | Some x -> W_Int (Some (Int63.(x + o)))
	  | _ -> W_Int None)  
      | W_Int (None, o) -> (W_Int (Some o))
      | W_Real (None, o) -> (W_Real (Some o))
	
    let ub_of_movar r' = function
      | W_Real (Some v, o) -> 
	(match (S.get_real_ub_local r' v) with
          | Some x -> W_Real (Some (Float.(x + o)))
          | _ -> W_Real None)
      | W_Int (Some v, o) -> 
	(match (S.get_ub_local r' v) with
	  | Some x -> W_Int (Some (Int63.(x + o)))
	  | _ -> W_Int None)  
      | W_Int (None, o) -> (W_Int (Some o))
      | W_Real (None, o) -> (W_Real (Some o))


    let bounds_of_row r' =
      let f ov = lb_of_ovar r' ov, ub_of_ovar r' ov in
      Array.map ~f

    let bounds_of_mixed_row r' =
      let f ov = lb_of_movar r' ov, ub_of_movar r' ov in
      Array.map ~f

    let bounds_within_for_dim (lb, ub) (lb', ub') =
      (LL.(lb' <= lb) && LU.(lb <= ub')) ||
        (LU.(lb' <= ub) && UU.(ub <= ub'))

    let bounds_within_for_mixed_dim 
	((lb, ub)  : mvar_bound * mvar_bound) 
	((lb', ub'): mvar_bound * mvar_bound) =
      (MLL.(lb' <= lb) && MLU.(lb <= ub')) ||
        (MLU.(lb' <= ub) && MUU.(ub <= ub'))

    let bounds_within_for_dim b b' =
      bounds_within_for_dim b b' || bounds_within_for_dim b' b

    let bounds_within_for_mixed_dim b b' =
      bounds_within_for_mixed_dim b b' || bounds_within_for_mixed_dim b' b


    let lb_of_diff {r_diff_h} r' v1 v2 =
      if Imt.compare_ivar v1 v2 = 0 then
        Some Int63.zero
      else if Imt.compare_ivar v1 v2 < 0 then
        let open Option in
        Hashtbl.find r_diff_h (v1, v2) >>= S.get_lb_local r'
      else
        let open Option in
        Hashtbl.find r_diff_h (v2, v1) >>=
          S.get_ub_local r' >>| Int63.neg


    let lb_of_mdiff_aux r = function
      | (W_Int v)  -> (match (S.get_lb_local r v) with 
	                 | Some x -> W_Int (Some x)
			 | _ -> W_Int None)
      | (W_Real v) -> (match (S.get_real_lb_local r v) with
	                 | Some x -> W_Real (Some x)
			 | _ -> W_Real None)

    let ub_of_mdiff_aux r = function
      | (W_Int v)  -> (match (S.get_ub_local r v) with 
	                 | Some x -> W_Int (Some x)
			 | _ -> W_Int None)
      | (W_Real v) -> (match (S.get_real_ub_local r v) with
	                 | Some x -> W_Real (Some x)
			 | _ -> W_Real None)

    let negate_mixed = function
      | W_Int (Some x) -> W_Int (Some (Int63.neg x))
      | W_Real (Some x) -> W_Real (Some (Float.neg x))
      | W_Int None -> W_Int None
      | W_Real None -> W_Real None

    let lb_of_mdiff {r_mdiff_h} 
	(r' : S.ctx) 
	(v1 : mvar) 
	(v2 : mvar) =
      match v1, v2 with
	| W_Int x1, W_Int x2 ->
	  if Imt.compare_ivar x1 x2 = 0 then
	    (W_Int (Some Int63.zero))
	  else if (Imt.compare_ivar x1 x2) < 0 then	   
	    (match (Hashtbl.find r_mdiff_h (v1, v2)) with 
	      | Some x -> lb_of_mdiff_aux r' x
	      | None -> W_Int None)
	  else 
	    (match (Hashtbl.find r_mdiff_h (v1, v2)) with
	      | Some x -> negate_mixed (ub_of_mdiff_aux r' x)
	      | None -> W_Int None) 
	| W_Real x1, W_Real x2 -> 
	  if Imt.compare_rvar x1 x2 = 0 then
	    (W_Real (Some Float.zero))
	  else if Imt.compare_rvar x1 x2 < 0 then
	    (match (Hashtbl.find r_mdiff_h (v1,v2)) with
	      | Some x -> lb_of_mdiff_aux r' x
	      | None -> W_Real None) 
	  else 
	    (match (Hashtbl.find r_mdiff_h (v1,v2)) with
	      | Some x -> negate_mixed (ub_of_mdiff_aux r' x)
	      | None -> W_Real None)
	| _, _ -> raise (Failure "Unexpected case lb_of_mdiff") 

    let ub_of_diff {r_diff_h} r' v1 v2 =
      if Imt.compare_ivar v1 v2 = 0 then
        Some Int63.zero
      else if Imt.compare_ivar v1 v2 < 0 then
        let open Option in
        Hashtbl.find r_diff_h (v1, v2) >>= S.get_ub_local r'
      else
        let open Option in
        Hashtbl.find r_diff_h (v2, v1) >>=
          S.get_lb_local r' >>| Int63.neg

 let ub_of_mdiff {r_mdiff_h} 
     (r' : S.ctx)
     (v1 : mvar)
     (v2 : mvar) =
     match v1, v2 with
	| W_Int x1, W_Int x2 ->
	  if Imt.compare_ivar x1 x2 = 0 then
	    (W_Int (Some Int63.zero))
	  else if (Imt.compare_ivar x1 x2) < 0 then	   
	    (match (Hashtbl.find r_mdiff_h (v1, v2)) with 
	      | Some x -> ub_of_mdiff_aux r' x
	      | None -> W_Int None)
	  else 
	    (match (Hashtbl.find r_mdiff_h (v1, v2)) with
	      | Some x -> negate_mixed (lb_of_mdiff_aux r' x)
	      | None -> W_Int None) 
	| W_Real x1, W_Real x2 -> 
	  if Imt.compare_rvar x1 x2 = 0 then
	    (W_Real (Some Float.zero))
	  else if Imt.compare_rvar x1 x2 < 0 then
	    (match (Hashtbl.find r_mdiff_h (v1,v2)) with
	      | Some x -> ub_of_mdiff_aux r' x
	      | None -> W_Real None) 
	  else 
	    (match (Hashtbl.find r_mdiff_h (v1,v2)) with
	      | Some x -> negate_mixed (lb_of_mdiff_aux r' x)
	      | None -> W_Real None)
	| _, _ -> raise (Failure "Unexpected case ub_of_mdiff")


    let bounds_within a a' =
      Array.for_all2_exn a a' ~f:bounds_within_for_dim

    let mixed_bounds_within 
	(a : mixed_bounds_array) 
	(a': mixed_bounds_array) =
      Array.for_all2_exn a a' ~f:bounds_within_for_mixed_dim

    let equal_row r r' row1 row2 =
      let f ov1 ov2 =
        match ov1, ov2 with
        | (Some v1, o1), (Some v2, o2) ->
          let lb = lb_of_diff r r' v1 v2
          and ub = ub_of_diff r r' v1 v2 in
          (match lb, ub with
          | Some lb, Some ub ->
            Int63.(lb = ub && lb = o2 - o1)
          | _, _ ->
            false)
        | (Some v1, o1), (None, o2) |
            (None, o2), (Some v1, o1) ->
          let lb = S.get_lb_local r' v1
          and ub = S.get_ub_local r' v1 in
          (match lb, ub with
          | Some lb, Some ub ->
            Int63.(lb = ub && lb = o2 - o1)
          | _ ->
            false)
        | (None, o1), (None, o2) ->
          Int63.(o1 = o2) in
      Array.for_all2_exn row1 row2 ~f   


 let equal_mixed_row 
     r 
     (r' : S.ctx)
     (row1 : mixed_row)
     (row2 : mixed_row) =
   let f ov1 ov2 =
     let faux lb ub o1 o2 = 
       (match lb, ub, o1, o2 with
         | W_Int (Some lb), W_Int (Some ub), W_Int o1, W_Int o2 ->
	   Int63.(lb = ub) && Int63.(lb = o2 - o1)
         | W_Real (Some lb), W_Real (Some ub), W_Real o1, W_Real o2 ->
	   Float.(lb = ub && lb = o2 - o1)
	 | _, _, _, _ ->
	   false) in
     (match ov1, ov2 with
       | W_Int (Some v1, o1), W_Int (Some v2, o2) ->
         let lb = lb_of_mdiff r r' (W_Int v1) (W_Int v2)
         and ub = ub_of_mdiff r r' (W_Int v1) (W_Int v2) in
         faux lb ub (W_Int o1) (W_Int o2)	      
       | W_Int (Some v1, o1), W_Int (None, o2)
       | W_Int (None, o2), W_Int (Some v1, o1) ->
	 let lb = lb_of_mdiff_aux r' (W_Int v1)
         and ub = ub_of_mdiff_aux r' (W_Int v1) in
	 faux lb ub (W_Int o1) (W_Int o2)
       | W_Real (Some v1, o1), W_Real (Some v2, o2) ->
         let lb = lb_of_mdiff r r' (W_Real v1) (W_Real v2)
         and ub = ub_of_mdiff r r' (W_Real v1) (W_Real v2) in
	 faux lb ub (W_Real o1) (W_Real o2)
       | W_Real (Some v1, o1), W_Real (None, o2)
       | W_Real (None, o2), W_Real (Some v1, o1) ->
	 let lb = lb_of_mdiff_aux r' (W_Real v1)
         and ub = ub_of_mdiff_aux r' (W_Real v1) in
         faux lb ub (W_Real o1) (W_Real o2)
       | W_Int (None, o1), W_Int (None, o2) ->
	 Int63.(o1 = o2)
       | W_Real (None, o1), W_Real (None, o2)->
         Float.(o1 = o2)
       | W_Int _ , W_Real _ 
       | W_Real _, W_Int _ ->
	 raise (Failure "Unexpected comparison equal_mixed_row")) in
   Array.for_all2_exn row1 row2 ~f

    let maybe_equal_rows r r' row a row' a' =
      bounds_within a a' &&
        (Array.for_all2_exn row row'
           ~f:(fun ov1 ov2 ->
             match ov1, ov2 with
             | (Some v1, o1), (Some v2, o2) ->
               let open Int63 in
               let d = o2 - o1
               and lb = lb_of_diff r r' v1 v2
               and ub = ub_of_diff r r' v1 v2
               and default = true in
               Option.value_map lb ~f:((>=) d) ~default &&
                 Option.value_map ub ~f:((<=) d) ~default
             | _ ->
               true))

 let maybe_equal_mixed_rows 
     (r : ctx) 
     (r' : S.ctx) 
     (row : mixed_row) 
     (a : mixed_bounds_array)  
     (row':mixed_row) 
     (a' : mixed_bounds_array) =
      mixed_bounds_within a a' &&
        (Array.for_all2_exn row row'
           ~f:(fun ov1 ov2 ->
	     let ge_mixed dif = (function
	       | W_Int (Some x) -> Float.(>=) dif (Int63.to_float x)
	       | W_Real (Some x) -> Float.(>=) dif x
	       | _ -> true)	    
	     and le_mixed dif = (function
	       | W_Int (Some x)  -> Float.(<=) dif (Int63.to_float x)
	       | W_Real (Some x) -> Float.(<=) dif x
	       | _ -> true) in
             match ov1, ov2 with
               | W_Int (Some v1, o1), W_Int (Some v2, o2) ->
		 let d = Int63.(to_float(o2 - o1))
		 and lb = lb_of_mdiff r r' (W_Int v1) (W_Int v2)
		 and ub = ub_of_mdiff r r' (W_Int v1) (W_Int v2) in    
		 (ge_mixed d lb) && (le_mixed d ub)
	       | W_Real (Some v1, o1), W_Real (Some v2, o2) ->
		 let d = Float.(o2 - o1)
		 and lb = lb_of_mdiff r r' (W_Real v1) (W_Real v2)
		 and ub = ub_of_mdiff r r' (W_Real v1) (W_Real v2) in    
		 (ge_mixed d lb) && (le_mixed d ub)
               | _ ->
		 true))

    let fold_index
        (m1, m2, l : index)
        ~init ~(f : 'a folded_no_bounds) =
      let f acc data = f data ~acc in
      let f ~key ~data init = List.fold_left data ~init ~f
      and init = List.fold_left l ~f ~init in
      let init = Map.fold m1 ~init ~f in
      Map.fold m2 ~init ~f

    let fold_mixed_index
        (m1, m2, l : mixed_index)
        ~init 
	~(f : 'a mixed_folded_no_bounds) =
      let f acc data = f data ~acc in
      let f ~key ~data init = List.fold_left data ~init ~f
      and init = List.fold_left l ~f ~init in
      let init = Map.fold m1 ~init ~f in
      Map.fold m2 ~init ~f

    let fold_candidates_list r r' row l i ~init ~(f : 'a folded) =
      let a = bounds_of_row r' row in
      let f acc data =
        let bounds = bounds_of_row r' data  in
        if maybe_equal_rows r r' data bounds row a then
          f data ~bounds ~acc
        else
          acc in
      List.fold_left l ~f ~init

    let fold_mixed_candidates_list 
	(r  : ctx)
	(r' : S.ctx) 
	(row: mixed_row) 
	l 
	(i : int) 
	~init 
	~(f : 'a mixed_folded) =
      let a = bounds_of_mixed_row r' row in
      let f acc (data:mixed_row) =
        let bounds = bounds_of_mixed_row r' data  in
        if maybe_equal_mixed_rows r r' data bounds row a then
          f data ~bounds ~acc
        else
          acc in
      List.fold_left l ~f ~init


    let fold_constant_candidates
        ({r_stats; r_mbounds_h} as r)
        r' row m i
        ~init ~(f : 'a folded) =
      r_stats.s_mbounds_all <- r_stats.s_mbounds_all + 1;
      let a = bounds_of_row r' row in
      let default () =
        r_stats.s_mbounds_fail <- r_stats.s_mbounds_fail + 1;
        let f acc data =
          let bounds = bounds_of_row r' data  in
          if maybe_equal_rows r r' data bounds row a then
            f data ~bounds ~acc
          else
            acc in
        let f ~key ~data init = List.fold_left data ~init ~f
        and min, max = a.(i) in
        let min = Option.value min ~default:Int63.min_value
        and max = Option.value max ~default:Int63.max_value in
        Map.fold_range_inclusive m ~min ~max ~init ~f
      and key = a, m in
      let r = Hashtbl.find_or_add r_mbounds_h key ~default in
      Tuple3.map1 r ~f:Array.copy

   

(** These functions extract a minimun/maximum given an iroption. For the cases None, the just returnmax/min value. Check if it's ok for the float case to return an integer. I understand that this won't affect the mapping but check again *)
  let extract_min (lb : mvar_bound) =
      match lb with
	| W_Int  (Some x) -> Int63.to_float x
	| W_Real (Some x) -> x
	| W_Int None | W_Real None -> Float.min_value

    let extract_max (ub: mvar_bound) = 
      match ub with
	| W_Int  (Some x) -> Int63.to_float x
	| W_Real (Some x) -> x
	| W_Int None | W_Real None -> Float.max_value 

  let fold_mixed_constant_candidates
        ({r_stats; r_mixbounds_h} as r)
        (r' : S.ctx)
	(row : mixed_row) 
	(m : mixed_row_map) 
	(i : int)
        ~init ~(f : 'a mixed_folded) =
      r_stats.s_mbounds_all <- r_stats.s_mbounds_all + 1;
      let a = bounds_of_mixed_row r' row in
      let default () =
        r_stats.s_mbounds_fail <- r_stats.s_mbounds_fail + 1;
        let f acc data =
          let bounds = bounds_of_mixed_row r' data  in
          if maybe_equal_mixed_rows r r' data bounds row a then
            f data ~bounds ~acc
          else
            acc in
        let f ~key ~data init = List.fold_left data ~init ~f
        and min, max = a.(i) in
        let min = extract_min min
        and max = extract_max max in
        Map.fold_range_inclusive m ~min ~max ~init ~f
      and key = a, m in
      let r = Hashtbl.find_or_add r_mixbounds_h key ~default in
      Tuple3.map1 r ~f:Array.copy

    
    let fold_candidates_map r r' row m i ~init ~(f : 'a folded) =
      let a = bounds_of_row r' row in
      let f acc data =
        let bounds = bounds_of_row r' data  in
        if maybe_equal_rows r r' data bounds row a then
          f data ~bounds ~acc
        else
          acc in
      let f ~key ~data init = List.fold_left data ~init ~f
      and min, max = a.(i) in
      let min = Option.value min ~default:Int63.min_value
      and max = Option.value max ~default:Int63.max_value in
      Map.fold_range_inclusive m ~min ~max ~init ~f

 let fold_candidates_mixed_map
     (r : ctx)
     (r':S.ctx)
     (row : mixed_row)
     (m : mixed_row_map)
     (i : int)
     ~init 
     ~(f : 'a mixed_folded) =
      let a = bounds_of_mixed_row r' row in
      let f acc data =
        let bounds = bounds_of_mixed_row r' data  in
        if maybe_equal_mixed_rows r r' data bounds row a then
          f data ~bounds ~acc
        else
          acc in
      let f ~key ~data init = List.fold_left data ~init ~f
      and min, max = a.(i) in
      let min = extract_min min
      and max = extract_max max in
      Map.fold_range_inclusive m ~min ~max ~init ~f

    let exists_candidate
        r r' (row, (m1, m2, l), i, _) ~(f : bool mapped) =
      let a = bounds_of_row r' row in
      let f data =
        let bounds = bounds_of_row r' data  in
        maybe_equal_rows r r' data bounds row a &&
          f data ~bounds in
      let f ~key ~data acc = acc || List.exists data ~f
      and init = List.exists l ~f in
      init ||
        let min = lb_of_ovar r' row.(i)
        and max = ub_of_ovar r' row.(i) in
        let min = Option.value min ~default:Int63.min_value
        and max = Option.value max ~default:Int63.max_value in
        let init = false in
        Map.fold_range_inclusive m1 ~min ~max ~init ~f ||
          Map.fold_range_inclusive m2 ~min ~max ~init ~f

    let exists_mixed_candidate
        r r' (row, (m1, m2, l), i, _) ~(f : bool mixed_mapped) =
      let a = bounds_of_mixed_row r' row in
      let f data =
        let bounds = bounds_of_mixed_row r' data  in
        maybe_equal_mixed_rows r r' data bounds row a &&
          f data ~bounds in
      let f ~key ~data acc = acc || List.exists data ~f
      and init = List.exists l ~f in
      init ||
        let min = lb_of_movar r' row.(i)
        and max = ub_of_movar r' row.(i) in
        let min = extract_min min
        and max = extract_max max in
        let init = false in
        Map.fold_range_inclusive m1 ~min ~max ~init ~f ||
          Map.fold_range_inclusive m2 ~min ~max ~init ~f


    let response_of_attempts a b =
      match a, b with
      | `Infeasible, _ | _, `Infeasible ->
        N_Unsat
      | `Tightened, _ | _, `Tightened ->
        N_Tightened
      | `Ok, `Ok ->
        N_Ok

    let maybe_upper_bound_ovar r r' ub (v, o) =
      match ub, v with
      | None, _ ->
        `Ok
      | Some ub, Some v ->
        S.set_ub_local r' v Int63.(ub - o)
      | Some ub, None ->
        if Int63.(ub >= o) then `Ok else `Infeasible

    let maybe_mixed_upper_bound_ovar 
	(r : ctx) 
	(r':S.ctx)
	(ub: mvar_bound)
	 v =
      match ub, v with
	| W_Int  None, (W_Int _) -> `Ok
	| W_Real None, (W_Real _) -> `Ok
	| W_Int (Some ub), W_Int (Some v, o) ->
	  S.set_ub_local r' v Int63.(ub - o)
	| W_Real (Some ub), W_Real (Some v, o) ->
	  S.set_real_ub_local r' v Float.(ub - o)
	| W_Int (Some ub), W_Int (None, o) ->
	  if Int63.(ub >= o) then `Ok else `Infeasible
	| W_Real (Some ub), W_Real (None, o) ->
	  if Float.(ub >= o) then `Ok else `Infeasible
	| _, _ -> raise (Unreachable.Exn _here_)


    let maybe_lower_bound_ovar r r' lb (v, o) =
      match lb, v with
      | None, _ ->
        `Ok
      | Some lb, Some v ->
        S.set_lb_local r' v Int63.(lb - o)
      | Some lb, None ->
        if Int63.(lb <= o) then `Ok else `Infeasible

    let maybe_mixed_lower_bound_ovar 
	(r : ctx) 
	(r':S.ctx)
	(lb: mvar_bound)
	v =
      match lb, v with
	| W_Int None , (W_Int _) -> `Ok
	| W_Real None, (W_Real _) -> `Ok
	| W_Int (Some lb), W_Int (Some v, o) ->
	  S.set_lb_local r' v Int63.(lb - o)
	| W_Real (Some lb), W_Real (Some v, o) ->
	  S.set_real_lb_local r' v Float.(lb - o)
	| W_Int (Some lb), W_Int (None, o) ->
	  if Int63.(lb <= o) then `Ok else `Infeasible
	| W_Real (Some lb), W_Real (None, o) ->
	  if Float.(lb <= o) then `Ok else `Infeasible
	| _, _ -> raise (Unreachable.Exn _here_)


    let foldi_responses_occs {r_occ_h} v ~f =
      match Hashtbl.find r_occ_h v with
      | None ->
        if true then raise (Unreachable.Exn _here_);
        N_Ok
      | Some d ->
        let n = Dequeue.back_index d in
        let n = Option.value_exn n ~here:_here_ in
        let rec g i acc =
          if i <= n then
            match Dequeue.get_opt d i with
            | Some (_, _, _, {contents = _} as o) ->
              (match f i o with
              | N_Unsat ->
                N_Unsat
              | N_Tightened ->
                g (i + 1) N_Tightened 
              | N_Ok ->
                g (i + 1) acc)
            | None ->
              raise (Unreachable.Exn _here_)
          else
            acc in
        let n = Dequeue.front_index d in
        let n = Option.value_exn n ~here:_here_ in
        g n N_Ok


    let foldi_responses_mixed_occs {r_mocc_h} v ~f =
      match Hashtbl.find r_mocc_h v with
	| None ->
          if true then raise (Unreachable.Exn _here_);
          N_Ok
	| Some d ->
          let n = Dequeue.back_index d in
          let n = Option.value_exn n ~here:_here_ in
          let rec g i acc =
            if i <= n then
              match Dequeue.get_opt d i with
		| Some (_, _, _, {contents = _} as o) ->
		  (match f i o with
		    | N_Unsat ->
                      N_Unsat
		    | N_Tightened ->
                      g (i + 1) N_Tightened 
		    | N_Ok ->
                      g (i + 1) acc)
		| None ->
		  raise (Unreachable.Exn _here_)
            else
              acc in
          let n = Dequeue.front_index d in
          let n = Option.value_exn n ~here:_here_ in
          g n N_Ok


    let for_all_occs {r_occ_h} v ~f =
      match Hashtbl.find r_occ_h v with
      | None ->
        true
      | Some d ->
        Dequeue.for_all d ~f

    let exists_occs {r_occ_h} v ~f =
      match Hashtbl.find r_occ_h v with
      | None ->
        false
      | Some d ->
        dequeue_exists_with_swap d ~f


    let for_all_mixed_occs {r_mocc_h} v ~f =
      match Hashtbl.find r_mocc_h v with
	| None ->
          true
	| Some d ->
          Dequeue.for_all d ~f

    let exists_mixed_occs {r_mocc_h} v ~f =
      match Hashtbl.find r_mocc_h v with
	| None ->
          false
	| Some d ->
          dequeue_exists_with_swap d ~f

    let satisfied_occ r r' (row, _, _, _ as occ) =
      let f row' ~bounds = equal_row r r' row row' in
      exists_candidate r r' occ ~f

    let satisfied_mixed_occ r r' (row, _, _, _ as mocc) =
      let f row' ~bounds = equal_mixed_row r r' row row' in
      exists_mixed_candidate r r' mocc ~f


(********************************************************** Propagate **********************************************************************)


(** Pure Integer *)

    type bp = Int63.t option * Int63.t option
    with sexp_of

    let approx_candidates_folded
        ?cnst_only:(cnst_only = false)
        r r' witness_row row ~bounds ~acc:(a, z, s) =
      Array.iteri bounds
        ~f:(fun i (lb, ub) ->
          let lb', ub' = a.(i) in
          if cnst_only then
            match lb, ub with
            | Some lb, Some ub when Int63.compare lb ub = 0 ->
              a.(i) <- (Option.(lb' >>| Int63.min lb),
                        Option.(ub' >>| Int63.max ub))
            | _, _ ->
              ()
          else
            a.(i) <- (Option.map2 lb lb' ~f:Int63.min,
                      Option.map2 ub ub' ~f:Int63.max));
      let equal =
        let eq1 v1 v2 = Imt.compare_ivar v1 v2 = 0 in
        let eq1 = Option.equal eq1
        and eq2 = Int63.equal in
        let equal = Tuple2.equal ~eq1 ~eq2 in
        Array.equal ~equal
      and s = s || equal_row r r' witness_row row in
      a, Zom.update z row ~equal, s

    let approx_candidates
        ?cnst_only:(cnst_only = false)
        r r' (row, (m1, m2, l), i, _) =
      let n = Array.length row
      and p = Some Int63.max_value, Some Int63.min_value in
      let init = Array.init ~f:(fun _ -> p) n, Zom.Z0, false
      and f = approx_candidates_folded ~cnst_only r r' row in
      let init = fold_constant_candidates r r' row m1 i ~init ~f in
      let init = fold_candidates_map r r' row m2 i ~init ~f in
      fold_candidates_list r r' row l i ~init ~f

    let fix_variable r v x =
      response_of_attempts
        (S.set_lb_local r v x)
        (S.set_ub_local r v x)

    let assert_ovar_equal {r_diff_h} r' (v1, o1) (v2, o2) =
      let fb b = if b then N_Ok else N_Unsat
      and f v1 v2 x =
        assert (Imt.compare_ivar v1 v2 < 0);
        let v = Hashtbl.find r_diff_h (v1, v2) in
        let v = Option.value_exn v ~here:_here_ in
        fix_variable r' v x
      and d = Int63.(o2 - o1) in
      match v1, v2 with
      | Some v1, Some v2 ->
        if Imt.compare_ivar v1 v2 = 0 then
          fb (Int63.equal o1 o2)
        else if Imt.compare_ivar v1 v2 > 0 then
          f v2 v1 (Int63.neg d)
        else
          f v1 v2 d
      | Some v1, None ->
        fix_variable r' v1 d
      | None, Some v2 ->
        fix_variable r' v2 Int63.(neg d)
      | None, None ->
        fb (Int63.equal o1 o2)


    type db_bounds = (Int63.t option * Int63.t option) list
    with sexp_of

    type occ_state = db_bounds * db_bounds list
    with sexp_of

    let row_state r r' row =
      let f ov = lb_of_ovar r' ov, ub_of_ovar r' ov in
      List.map (Array.to_list row) ~f

    let index_state r r' (ix : index) =
      let init = [] and f row ~acc = row_state r r' row :: acc in
      fold_index ix ~init ~f

    let occ_state r r' (row, index, i, {contents = i'} : occ) =
      row_state r r' row, index_state r r' index

    let propagate_for_occ ({r_level} as r) r' = function
      | _, _, _, {contents = Some _} ->
        N_Ok
      | row, _, i, s as occ ->
        match approx_candidates r r' occ with
        | _, Zom.Z0, _ ->
          (* no candidates *)
          N_Unsat
        | _, Zom.Z1 row2, b ->
          (* propagate bounds *)
          if b then s := Some r_level;
          let f i = assert_ovar_equal r r' row.(i) in
          array_foldi_responses row2 ~f
        | a, Zom.Zn _, b ->
          if b then s := Some r_level;
          array_foldi_responses a
            ~f:(fun i (lb, ub) ->
              let rl = maybe_lower_bound_ovar r r' lb row.(i)
              and ru = maybe_upper_bound_ovar r r' ub row.(i) in
              response_of_attempts rl ru)

    let propagate_for_occ r r' occ =
      propagate_for_occ r r' occ |>
          intercept_response "propagate_for_occ"

    let propagate_for_bvar_aux r r' v =
      (let f _ = propagate_for_occ r r' in
       foldi_responses_occs r v ~f) |>
          intercept_response "propagate_for_bvar_aux"

	
    let propagate_for_bvar r r' v =
      let f = function
        | true ->
          propagate_for_bvar_aux r r' v
        | false ->
          N_Ok
      and default = N_Ok in
      S.bderef_local r' v |>
          Option.value_map ~f ~default |>
              intercept_response "propagate_for_bvar"

	
(** Mixed Int/Real *)

    type bp_mixed = mvar_bound * mvar_bound
    with sexp_of

    let map2 (x : mvar_bound) (y : mvar_bound) 
	~(fint:(Int63.t -> Int63.t -> Int63.t)) 
	~(freal:(Float.t -> Float.t -> Float.t)) =
      match x, y with
	| W_Int (Some x), W_Int (Some y) ->
	  W_Int (Some (fint x y))
	| W_Real (Some x), W_Real (Some y) ->
	  W_Real (Some (freal x y))
	| W_Int None, W_Int None -> 
	  W_Int None
	| W_Real None, W_Real None->
	  W_Real None
	| _, _ -> raise (Failure "Undefined case for map2 mvar_bound")

 let approx_mixed_candidates_folded
        ?cnst_only:(cnst_only = false)
        (r : ctx) 
	(r': S.ctx)
	(witness_row: mixed_row)
	(row: mixed_row) 
	~(bounds: mixed_bounds_array) 
	~acc:(a, z, s) =
      Array.iteri bounds
        ~f:(fun i (lb, ub) ->
          let lb', ub' = a.(i) in
          if cnst_only then
            match lb, ub, lb', ub' with
            | W_Int (Some lb), W_Int (Some ub), W_Int (Some lb'), W_Int (Some ub') 
	      when Int63.compare lb ub = 0 ->
              a.(i) <- (W_Int (Some (Int63.min lb lb')), W_Int (Some (Int63.max ub ub')))
	    | W_Real (Some lb), W_Real (Some ub), W_Real (Some lb'), W_Real (Some ub')
	      when Float.compare lb ub = 0 ->
	      a.(i) <- (W_Real (Some (Float.min lb lb')), W_Real (Some (Float.max ub ub')))
            | _, _, _, _ ->
              ()
          else
            a.(i) <- (map2 lb lb' (Int63.min) (Float.min),
		      map2 ub ub' (Int63.max) (Float.max))
	);
   let equal =
     let equal v1 v2 = 
       (match v1, v2 with
	 | W_Int (v1,o1), W_Int (v2,o2) -> 
	   Option.equal (fun x1 x2 -> Imt.compare_ivar x1 x2 = 0) v1 v2 && Int63.(o1 = o2)
         | W_Real (v1,o1), W_Real (v2,o2) -> 
	   Option.equal (fun x1 x2 -> Imt.compare_rvar x1 x2 = 0) v1 v2 && Float.(o1 = o2)
	 | _, _ -> false)
     in
     Array.equal ~equal
   and s = s || equal_mixed_row r r' witness_row row in
   a, Zom.update z row ~equal, s


    let approx_mixed_candidates
        ?cnst_only:(cnst_only = false)
        (r : ctx) 
	(r': S.ctx) 
	((row : mixed_row), (m1, m2, l), i, _) =     
      let fmap v = (match v with
	| W_Int (_, _)  -> 
	  (W_Int (Some (Int63.max_value)) , W_Int (Some (Int63.min_value))) 
	| W_Real (_, _) -> 
	  (W_Real (Some (Float.max_value)), W_Real (Some (Float.min_value)))) in
      let init_array = Array.map fmap row in
      let init = init_array, Zom.Z0, false
      and f = approx_mixed_candidates_folded ~cnst_only r r' row in
      let init = fold_mixed_constant_candidates r r' row m1 i ~init ~f in
      let init = fold_candidates_mixed_map r r' row m2 i ~init ~f in
      fold_mixed_candidates_list r r' row l i ~init ~f

    let fix_mixed_variable r v x = 
      let r1, r2 =  match v, x with 
	| W_Int v, W_Int x  -> 
	  S.set_lb_local r v x, S.set_ub_local r v x
	| W_Real v, W_Real x -> 
	  S.set_real_lb_local r v x, S.set_real_ub_local r v x 
	| _, _ -> raise (Unreachable.Exn _here_) in
      response_of_attempts r1 r2

    let assert_mixed_ovar_equal {r_mdiff_h} r' v1 v2 =
      let fb b = if b then N_Ok else N_Unsat
      and f v1 v2 (x : (Int63.t, Float.t) ireither) =
	match v1, v2, x with
	  | W_Int v1, W_Int v2, W_Int x -> 
            assert (Imt.compare_ivar v1 v2 < 0);
            let v = Hashtbl.find r_mdiff_h (W_Int v1, W_Int v2) in
            let v = Option.value_exn v ~here:_here_ in
            fix_mixed_variable r' v (W_Int x)
	  | W_Real v1, W_Real v2, W_Real x ->
	    assert (Imt.compare_rvar v1 v2 < 0);
	    let v = Hashtbl.find r_mdiff_h (W_Real v1, W_Real v2) in
	    let v = Option.value_exn v ~here:_here_ in
	    fix_mixed_variable r' v (W_Real x)     
	  | _ , _, _ -> raise (Failure "Undefined case for assert_mixed_ovar_equal")
      in
      match v1, v2 with
      | W_Int (Some v1, o1), W_Int (Some v2, o2) ->
        if Imt.compare_ivar v1 v2 = 0 then
          fb (Int63.equal o1 o2)
        else if Imt.compare_ivar v1 v2 > 0 then
          f (W_Int v2) (W_Int v1) (W_Int (Int63.(o1 - o2)))
        else
          f (W_Int v1) (W_Int v2) (W_Int (Int63.(o2 - o1)))
      | W_Real (Some v1, o1), W_Real (Some v2, o2) ->
	if Imt.compare_rvar v1 v2 = 0 then
	  fb (Float.equal o1 o2)
	else if Imt.compare_rvar v1 v2 > 0 then 
	  f (W_Real v2) (W_Real v1) (W_Real (Float.(o1 - o2)))
	else 
	  f (W_Real v1) (W_Real v2) (W_Real (Float.(o1 - o2)))
      | W_Int (Some v1, o1), W_Int (None, o2) ->
        fix_mixed_variable r' (W_Int v1) (W_Int (Int63.(o2 - o1)))
      | W_Int (None,o1), W_Int (Some v2,o2) ->
        fix_mixed_variable r' (W_Int v2) (W_Int (Int63.(o1 - o2)))
      | W_Int (None, o1), W_Int (None, o2) -> 
        fb (Int63.equal o1 o2)
      | W_Real (None,o1), W_Real (None,o2) ->
        fb (Float.equal o1 o2)
      | W_Real (Some v1, o1), W_Real (None, o2) ->
	fix_mixed_variable r' (W_Real v1) (W_Real Float.(o2 - o1))
      | W_Real (None, o1), W_Real (Some v2, o2) -> 
	fix_mixed_variable r' (W_Real v2) (W_Real Float.(o1 - o2))
      | _, _ -> raise (Failure "Undefined case (2) for assert_mixed_ovar_equal")


    type mixed_db_bounds = (mvar_bound * mvar_bound) list
    with sexp_of

    type mocc_state = mixed_db_bounds * mixed_db_bounds list
    with sexp_of

    let mixed_row_state r r' (row : mixed_row) = 
      let f ov = lb_of_movar r' ov, ub_of_movar r' ov in
      List.map (Array.to_list row) ~f

    let mixed_index_state r r' (ix : mixed_index) =
      let init = [] and f row ~acc = mixed_row_state r r' row :: acc in
      fold_mixed_index ix ~init ~f

    let mocc_state r r' (row, index, i, {contents = i'} : mixed_occ) =
      mixed_row_state r r' row, mixed_index_state r r' index

    let propagate_for_mocc ({r_level} as r) r' = function
      | _, _, _, {contents = Some _} ->
        N_Ok
      | row, _, i, s as mocc ->
        match approx_mixed_candidates r r' mocc with
        | _, Zom.Z0, _ ->
          (* no candidates *)
          N_Unsat
        | _, Zom.Z1 row2, b ->
          (* propagate bounds *)
          if b then s := Some r_level;
          let f i = assert_mixed_ovar_equal r r' row.(i) in
          array_foldi_responses row2 ~f
        | a, Zom.Zn _, b ->
          if b then s := Some r_level;
          array_foldi_responses a
            ~f:(fun i (lb, ub) ->
              let rl = maybe_mixed_lower_bound_ovar r r' lb row.(i)
              and ru = maybe_mixed_upper_bound_ovar r r' ub row.(i) in
              response_of_attempts rl ru)

    let propagate_for_mocc r r' mocc = 
      intercept_response "propagate_for_mocc"
	(propagate_for_mocc r r' mocc)

    let propagate_for_mixed_bvar_aux r r' v =
      intercept_response "propagate_for_mixed_bvar_aux"
        (let f _ = propagate_for_mocc r r' in
         foldi_responses_mixed_occs r v ~f)

    let propagate_for_mixed_bvar r r' v =
      intercept_response "propagate_for_mixed_bvar"
        (Option.value_map (S.bderef_local r' v)
           ~f:(function true ->
             propagate_for_mixed_bvar_aux r r' v
             | false ->
               N_Ok)
           ~default:N_Ok)


    let propagate ({r_stats; r_bvar_d; r_ismixed} as r) r' =
      r_stats.s_propagate <- r_stats.s_propagate + 1;
      if r_ismixed then
	(let f = propagate_for_mixed_bvar r r' in
	dequeue_fold_responses r_bvar_d ~f) |>
		intercept_response "propagate_mixed"
      else 
	(let f = propagate_for_bvar r r' in
	 dequeue_fold_responses r_bvar_d ~f) |>
	 	intercept_response "propagate"


   (* let propagate_mixed ({r_stats; r_bvar_d} as r) r' =
      r_stats.s_propagate <- r_stats.s_propagate + 1;
      let f = propagate_for_mixed_bvar r r' in
      intercept_response "propagate_mixed"
        (dequeue_fold_responses r_bvar_d ~f)
    *)
(********************************** check given solution ***********************************************************************************)
        
(**   Pure Integer   *)
        
    let deref_ovar_sol r' sol = function
      | Some v, o ->
        Int63.(S.ideref_sol r' sol v + o)
      | None, o ->
        o

    let matches_row r' sol row_concrete row =
      Array.for_all2_exn row row_concrete
        ~f:(fun ov c -> Int63.equal (deref_ovar_sol r' sol ov) c)

    let exists_index (m1, m2, l) ~f ~min ~max =
      List.exists l ~f ||
        let f ~key ~data acc = acc || List.exists data ~f in
        Map.fold_range_inclusive m1 ~min ~max ~init:false ~f ||
          Map.fold_range_inclusive m2 ~min ~max ~init:false ~f 

    let check_for_occ r r' sol ((row, index, i, _) : occ) =
      let row = Array.map row ~f:(deref_ovar_sol r' sol) in
      let f = matches_row r' sol row in
      exists_index index ~min:row.(i) ~max:row.(i) ~f

    let check_for_bvar ({r_occ_h} as r) r' sol v =
      not (S.bderef_sol r' sol v) ||
        for_all_occs r v ~f:(check_for_occ r r' sol)
           
      
(**   Mixed Int/Real   *)

    let deref_mvar_sol r' sol = function
      | W_Int (Some v, o) ->
        Int63.(to_float(S.ideref_sol r' sol v + o))
      | W_Real (Some v, o) ->
	Float.(S.rderef_sol r' sol v + o)
      | W_Int (None, o) ->
        Int63.to_float o
      | W_Real (None, o) -> 
	o

    let matches_mixed_row r' sol row_concrete row =
      Array.for_all2_exn row row_concrete
        ~f:(fun ov c -> Float.equal (deref_mvar_sol r' sol ov) c)

    let exists_mixed_index (m1, m2, l) ~f ~(min:Float.t) ~(max:Float.t) =
      List.exists l ~f ||
        let f ~key ~data acc = acc || List.exists data ~f in
        Map.fold_range_inclusive m1 ~min ~max ~init:false ~f ||
          Map.fold_range_inclusive m2 ~min ~max ~init:false ~f


    let check_for_mocc r r' sol ((row, index, i, _) : mixed_occ) =
      let row = Array.map row ~f:(deref_mvar_sol r' sol) in
      let f = matches_mixed_row r' sol row 
      and min = row.(i) 
      and max = row.(i) in
      exists_mixed_index index ~min ~max ~f

    let check_for_bvar_mixed ({r_mocc_h} as r) r' sol v =
      not (S.bderef_sol r' sol v) ||
	for_all_mixed_occs r v ~f:(check_for_mocc r r' sol)

    (*let check_mixed ({r_stats; r_bvar_d} as r) r' sol =
      r_stats.s_check <- r_stats.s_check + 1;
      let f = check_for_bvar_mixed r r' sol in
      intercept_bool "check_mixed" (Dequeue.for_all r_bvar_d ~f)

*)

let check ({r_stats; r_bvar_d} as r) r' sol =
      r_stats.s_check <- r_stats.s_check + 1;
      if r.r_ismixed 
      then let f = check_for_bvar_mixed r r' sol in
	  Dequeue.for_all r_bvar_d ~f |> intercept_bool "check_mixed"
      else let f = check_for_bvar r r' sol in
	  Dequeue.for_all r_bvar_d ~f |> intercept_bool "check"


(********************************************************* branching **********************************************************************)


(** Pure Integer *)

    let branch_for_bvar r r' v ~f =
      match S.bderef_local r' v with
      | Some true ->
        exists_occs r v ~f
      | _ ->
        false

    let branch {r_bvar_d} ~f =
      dequeue_exists_with_swap r_bvar_d ~f

    let branch_on_column r r' (lb, ub) ov n =
      let lb =
        let lb' = lb_of_ovar r' ov in
        if LL.(lb <= lb') then lb' else lb
      and ub =
        let ub' = ub_of_ovar r' ov in
        if UU.(ub' <= ub) then ub' else ub in
      let lb = Option.value_exn lb ~here:_here_
      and ub = Option.value_exn ub ~here:_here_ in
      not (Int63.(equal lb max_value)) &&
        not (Int63.(equal ub min_value)) &&
        not (Int63.equal lb ub) &&
        match ov with
        | Some v, o ->
          let middle = Int63.((lb + ub) / (one + one) - o) in
          let middle = Int63.to_float middle
          and range = Int63.to_float ub -. Int63.to_float lb in
          (if n <= 50 && Float.(range <= of_int 50) then
              (ignore range;
               middle +. 0.5)
           else
              middle) |> S.ibranch r' v |> bool_of_ok_or_fail
        | None, _ ->
          false

    let branch0_for_occ ?any:(any = false)
        r r' (row, _, i, _ as occ) =
      match
        approx_candidates r r' occ ~cnst_only:true
      with
      | _, (Zom.Z0 | Zom.Z1 _), _ ->
        false
      | a, Zom.Zn n, _ ->
        if any then
          let f b v = not (branch_on_column r r' b v n) in
          not (Array.for_all2_exn a row ~f)
        else
          branch_on_column r r' a.(i) row.(i) n

    let branch0_for_occ ?any:(any = false) r r' (_, _, _, s as occ) =
      match s with
      | {contents = Some _} ->
        false
      | _ ->
        branch0_for_occ ~any r r' occ

    let branch0 r r' =
      let f = branch0_for_occ ~any:false r r' in
      let f = branch_for_bvar r r' ~f in
      branch r ~f

    let branch0_5 r r' =
      let f = branch0_for_occ ~any:true r r' in
      let f = branch_for_bvar r r' ~f in
      branch r ~f


    let branch_on_diff {r_diff_h} r' (v1, o1) (v2, o2) =
      let doit v1 v2 x =
        let v = Hashtbl.find r_diff_h (v1, v2) in
        let v = Option.value_exn v ~here:_here_ in
        Int63.to_float x |> S.ibranch r' v |> bool_of_ok_or_fail
      and d = Int63.(o2 - o1) in
      match v1, v2 with
      | Some v1, Some v2 ->
        if Imt.compare_ivar v1 v2 = 0 then
          false
        else if Imt.compare_ivar v1 v2 > 0 then
          doit v2 v1 (Int63.neg d)
        else
          doit v1 v2 d
      | _, _ ->
        false

    let branch1_for_occ r r' (row, index, i, _ as occ) =
      let f row2 ~bounds =
        let f ov1 ov2 = not (branch_on_diff r r' ov1 ov2) in
        not (Array.for_all2_exn row row2 ~f) in
      exists_candidate r r' occ ~f

    let branch1_for_occ r r' (_, _, _, s as occ) =
      match s with
      | {contents = Some _} ->
        false
      | _ ->
        branch1_for_occ r r' occ


    let branch1 r r' =
      branch r ~f:(branch_for_bvar r r' ~f:(branch1_for_occ r r'))

    let branch2_for_bvar r r' v =
      not (Option.is_some (S.bderef_local r' v)) &&
        bool_of_ok_or_fail (S.bbranch r' v)

    let branch2 r r' =
      branch r ~f:(branch2_for_bvar r r')

    
(* Mixed Int / Real *)

    let branch_for_mixed_bvar r r' v ~f =
      match S.bderef_local r' v with
	| Some true ->
          exists_mixed_occs r v ~f
	| _ ->
          false

    let branch_mixed {r_bvar_d} ~f =
      dequeue_exists_with_swap r_bvar_d ~f

    let branch_on_mixed_column r r' (lb, ub) ov n =
      let lb =
        let lb' = lb_of_movar r' ov in
        if MLL.(lb <= lb') then lb' else lb
      and ub =
        let ub' = ub_of_movar r' ov in
        if MUU.(ub' <= ub) then ub' else ub in
      match lb, ub with
	| W_Int (Some lb), W_Int (Some ub) ->
	  not (Int63.(equal lb max_value)) &&
            not (Int63.(equal ub min_value)) &&
            not (Int63.equal lb ub) &&
            (match ov with
              | W_Int (Some v, o) ->
		let middle = Int63.((lb + ub) / (one + one) - o) in
		let middle = Int63.to_float middle
		and range = Int63.to_float ub -. Int63.to_float lb in
		(if n <= 50 && Float.(range <= of_int 50) then
		    (ignore range;
		     middle +. 0.5)
		 else
		    middle) |> S.ibranch r' v |> bool_of_ok_or_fail		    		
              | W_Int (None, _) ->
		false
	      | _  -> raise (Failure "Unexpected int value branch_on_mixed_column"))
	| W_Real (Some lb), W_Real (Some ub) ->
	    not (Float.(equal lb max_value)) &&
            not (Float.(equal ub min_value)) &&
            not (Float.equal lb ub) &&
	      (match ov with
		| W_Real (Some v, o) ->
		  let middle = Float.((lb + ub) / (2.0) - o)
		  and range = Float.(ub - lb) in
		  bool_of_ok_or_fail
		    (S.rbranch r' v
		       (if n <= 50 && Float.(range <= of_int 50) then
			   (ignore (range);
			    Float.(middle + 0.5))
			else
			   middle))
		| W_Real (None, _) ->
		  false
		| _ -> raise (Failure "Unexpected real value branch_on_mixed_column"))
	| _, _  -> raise (Failure "Unexpected case branch_on_mixed_column")
	     

    let branch0_for_mixed_occ ?any:(any = false)
        r r' (row, _, i, _ as mocc) =
      match
        approx_mixed_candidates r r' mocc ~cnst_only:true
      with
      | _, (Zom.Z0 | Zom.Z1 _), _ ->
        false
      | a, Zom.Zn n, _ ->
        if any then
          let f b v = not (branch_on_mixed_column r r' b v n) in
          not (Array.for_all2_exn a row ~f)
        else
          branch_on_mixed_column r r' a.(i) row.(i) n


    let branch0_for_mixed_occ ?any:(any = false) r r' (_, _, _, s as mocc) =
      match s with
      | {contents = Some _} ->
        false
      | _ ->
        branch0_for_mixed_occ ~any r r' mocc

    let branch0_mixed r r' =
      let f = branch0_for_mixed_occ ~any:false r r' in
      let f = branch_for_mixed_bvar r r' ~f in
      branch_mixed r ~f

    let branch0_5_mixed r r' =
      let f = branch0_for_mixed_occ ~any:true r r' in
      let f = branch_for_mixed_bvar r r' ~f in
      branch_mixed r ~f


    let branch_on_mixed_diff {r_mdiff_h} r' var1 var2 =
      let doit v1 v2 x =
	let v = Hashtbl.find r_mdiff_h (v1, v2) in
        let v = Option.value_exn v ~here:_here_ in
        (match v with 
	  | W_Int v  -> S.ibranch r' v x |> bool_of_ok_or_fail
	  | W_Real v -> S.rbranch r' v x |> bool_of_ok_or_fail)
      in      
      match var1, var2 with
      | W_Int (Some v1, o1), W_Int (Some v2, o2) ->
        if Imt.compare_ivar v1 v2 = 0 then
          false
        else if Imt.compare_ivar v1 v2 > 0 then
          doit (W_Int v2) (W_Int v1) (Int63.(to_float( neg (o2 - o1))))
        else
          doit (W_Int v1) (W_Int v2) (Int63.(to_float(o2 - o1)))
      | W_Real (Some v1, o1), W_Real (Some v2, o2) ->
	if Imt.compare_rvar v1 v2 = 0 then
	  false
	else if Imt.compare_rvar v1 v2 > 0 then 
	  doit (W_Real v2) (W_Real v1) (Float.(neg (o2 - o1)))
	else 
	  doit (W_Real v1) (W_Real v2) (Float.(o2 - o1))
      | _, _ ->
        false


    let branch1_for_mixed_occ r r' (row, index, i, _ as mocc) =
      let f row2 ~bounds =
        let f ov1 ov2 = not (branch_on_mixed_diff r r' ov1 ov2) in
        not (Array.for_all2_exn row row2 ~f) in
      exists_mixed_candidate r r' mocc ~f


    let branch1_for_mixed_occ r r' (_, _, _, s as mocc) =
      match s with
	| {contents = Some _} ->
          false
	| _ ->
          branch1_for_mixed_occ r r' mocc

    let branch1_mixed r r' =
      branch_mixed r ~f:(branch_for_mixed_bvar r r' ~f:(branch1_for_mixed_occ r r'))
  
    let branch2_mixed r r' =
      branch_mixed r ~f:(branch2_for_bvar r r')


    let branch_mixed ({r_stats} as r) r' =
      try
        r_stats.s_branch <- r_stats.s_branch + 1;
        ok_for_true
          (branch0_mixed r r' ||
             branch0_5_mixed r r' ||
             branch1_mixed r r' ||
             branch2_mixed r r')
      with
      | e ->
        (Exn.to_string e |> Printf.printf "exception: %s\n%!p";
         raise e)


let branch ({r_stats} as r) r' =
      try
        r_stats.s_branch <- r_stats.s_branch + 1;
	if r.r_ismixed then
	    (branch0_mixed r r' ||
               branch0_5_mixed r r' ||
               branch1_mixed r r' ||
               branch2_mixed r r') |> ok_for_true   
	else  
	    (branch0 r r' ||
               branch0_5 r r' ||
               branch1 r r' ||
               branch2 r r') |> ok_for_true
      with
      | e ->
        (Printf.printf "exception: %s\n%!p" (Exn.to_string e);
         raise e)

         
(* stack management *)

    let push_level ({r_stats} as r) _ =
      r.r_level <- r.r_level + 1;
      r.r_stats.s_maxdepth <- max r.r_stats.s_maxdepth r.r_level;
      r.r_stats.s_push_level <- r.r_stats.s_push_level + 1

    let backtrack ({r_occ_h; r_mocc_h; r_stats} as r) _ =
      assert (r.r_level >= 0);
      r.r_level <- r.r_level - 1;
      (let f ~key ~data =
         let f = function
           | (_, _, _, ({contents = Some c} as rf))
               when c >= r.r_level ->
             rf := None
           | _ ->
             () in
         Dequeue.iter data ~f in
       if r.r_ismixed 
       then Hashtbl.iter r_mocc_h ~f
       else Hashtbl.iter r_occ_h ~f);
      r_stats.s_backtrack <- r_stats.s_backtrack + 1

  end

end
