open Core.Std
open Terminology
open Core.Int_replace_polymorphic_compare

module Make

  (S : Imt_intf.S_access)
  (I : Id.Accessors) =

struct

  open Logic

  module P = Pre.Make(I)

  type c = I.c

  type 't term = (I.c, 't) M.t

  type formula = I.c A.t Formula.t

  (*

    Types come with boilerplate for comparison and sexp conversion.

    Type_conv can generate these automatically, but it breaks module
    definitions and recursive modules.

  *)

  let hashable_ivar = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = S.compare_ivar;
    sexp_of_t = S.sexp_of_ivar
  }

  let hashable_bvar = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = S.compare_bvar;
    sexp_of_t = S.sexp_of_bvar
  }

(* Added rvar for real variables. Check what happens with S.compare_rvar, S.sexp_of_rvar*)

(*  let hashable_rvar = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = S.compare_rvar;
    sexp_of_t = S.sexp_of_rvar
  }
*)
(*End here*)
    
  type fid = I.c Id.Box_arrow.t
  with compare, sexp_of

  let hashable_fid = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_fid;
    sexp_of_t = sexp_of_fid
  }

  type iid  = (I.c, int) Id.t
  with compare, sexp_of

  let hashable_iid = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_iid;
    sexp_of_t = sexp_of_iid
  }

  type bid = (I.c, bool) Id.t
  with compare, sexp_of

  let hashable_bid = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_bid;
    sexp_of_t = sexp_of_bid
  }

(*Added type for real variables *)
  type rid = (I.c, float) Id.t
  with compare, sexp_of

  let hashable_rid = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_rid;
    sexp_of_t = sexp_of_rid
  }
(*
  type mid =                        (*Remove*)
    | MID_R of (I.c, float) Id.t
    | MID_I of (I.c, int) Id.t
  with compare, sexp_of

  type mvar =                       (*Remove*)
    | MVAR_R of S.rvar
    | MVAR_I of S.ivar
  with compare, sexp_of

  let hashable_mid = {              (*Remove*)
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_mid;
    sexp_of_t = sexp_of_mid  
  }

  let hashable_mvar = {             (*Remove*) 
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_mvar;
    sexp_of_t = sexp_of_mvar
  }

  (* Mixed (Int + Float) offset variable*)      (*Remove*)
  type movar = mvar option offset
  with compare, sexp_of
*)
(* End here *)

  type ovar = S.ivar option offset
  with compare, sexp_of

  type rovar = S.ivar option roffset
  with compare, sexp_of
    
  type bg_call = S.f * ovar list
  with compare, sexp_of

  let compare_bg_call =
    Tuple2.compare
      ~cmp1:S.compare_f
      ~cmp2:(List.compare ~cmp:compare_ovar)

  let sexp_of_bg_call =
    Tuple2.sexp_of_t S.sexp_of_f (List.sexp_of_t sexp_of_ovar)

  let hashable_bg_call = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_bg_call;
    sexp_of_t = sexp_of_bg_call;
  }

  type bg_isum = S.ivar isum
  with compare, sexp_of

  let hashable_bg_isum = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash; 
    compare = compare_bg_isum;
    sexp_of_t = sexp_of_bg_isum;
  }

(* Added: list of float * rvar *)
  type bg_rsum = S.ivar rsum
  with compare, sexp_of

  let hashable_bg_rsum = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_bg_rsum;
    sexp_of_t = sexp_of_bg_rsum
  }

(*  type bg_msum = mvar rsum
  with compare, sexp_of

 let hashable_bg_msum = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = compare_bg_msum;
    sexp_of_t = sexp_of_bg_msum
  }
*)
(*end *)

  let type_of_term :
  type t . t term -> t Type.t =
    fun x -> M.type_of_t ~f:I.type_of_t' x

  let flat_sum_negate (l, x) =
    List.map l ~f:(Tuple2.map1 ~f:Int63.neg), Int63.neg x

  (* optional var, possibly negated (S_Pos None means true) *)

  type xvar = S.bvar option signed
  with compare, sexp_of

  let xtrue = S_Pos None

  let xfalse = S_Neg None

  (* standard MIP types *)

  let mip_type_int = T_Int (None, None)

  let mip_type_bool = T_Int (Some Int63.zero, Some Int63.one)

  let mip_type_real = T_Real (None, None)

  (* context *)

  type ctx = {
    r_ctx              :  S.ctx;
    r_pre_ctx          :  P.ctx;
    r_ivar_m           :  (iid, S.ivar) Hashtbl.t;
    r_bvar_m           :  (bid, S.bvar) Hashtbl.t;
    r_rvar_m           :  (rid, S.ivar) Hashtbl.t;   (*Added*)
    r_iid_m            :  (S.ivar, iid) Hashtbl.t;
    r_bid_m            :  (S.bvar, bid) Hashtbl.t;
    r_rid_m            :  (S.ivar, rid) Hashtbl.t;   (*Added*)
    r_xvar_m           :  (P.formula, xvar) Hashtbl.t;
    r_fun_m            :  (fid, S.f) Hashtbl.t;
    r_call_m           :  (bg_call, S.ivar) Hashtbl.t;
    r_sum_m            :  (P.sum, S.ivar iexpr) Hashtbl.t;
    r_msum_m           :  (P.suml, S.ivar rexpr) Hashtbl.t;   (*Added*)
    r_var_of_sum_m     :  (bg_isum, S.ivar) Hashtbl.t;      
    r_rvar_of_rsum_m   :  (bg_rsum, S.ivar) Hashtbl.t;  (*Added*)
    r_ovar_of_iite_m   :  (P.iite, ovar) Hashtbl.t;
    r_rovar_of_iite_m  :  (P.iite, rovar) Hashtbl.t;   (*Added*)
    r_q                :  P.formula Dequeue.t;
    mutable r_obj      :  P.term option;
    mutable r_fun_cnt  :  int;
    mutable r_unsat    :  bool
  }

  let make_ctx s = {
    r_ctx     = s;
    r_pre_ctx = P.make_ctx ();
    r_ivar_m  =
      Hashtbl.create ()  ~size:10240  ~hashable:hashable_iid;
    r_bvar_m  = 
      Hashtbl.create ()  ~size:10240  ~hashable:hashable_bid;
    r_rvar_m  =
      Hashtbl.create ()  ~size:10240  ~hashable:hashable_rid;
    r_iid_m =
      Hashtbl.create ()  ~size:10240  ~hashable:hashable_ivar;
    r_bid_m =
      Hashtbl.create ()  ~size:10240  ~hashable:hashable_bvar;
    r_rid_m =
      Hashtbl.create ()  ~size:10240  ~hashable:hashable_ivar;
    r_xvar_m  =
      Hashtbl.create ()  ~size:10240  ~hashable:P.hashable_formula;
    r_fun_m   =
      Hashtbl.create ()  ~size:512    ~hashable:hashable_fid;
    r_call_m  =
      Hashtbl.create ()  ~size:2048   ~hashable:hashable_bg_call;
    r_sum_m =
      Hashtbl.create ()  ~size:2048   ~hashable:P.hashable_sum;
    r_msum_m =
      Hashtbl.create ()  ~size:2048   ~hashable:P.hashable_suml; 
    r_var_of_sum_m =
      Hashtbl.create ()  ~size:2048   ~hashable:hashable_bg_isum;
    r_rvar_of_rsum_m =
      Hashtbl.create ()  ~size:2048   ~hashable:hashable_bg_rsum; 
    r_ovar_of_iite_m =
      Hashtbl.create ()  ~size:2048   ~hashable:P.hashable_iite;
    r_rovar_of_iite_m =
      Hashtbl.create ()  ~size:2048   ~hashable:P.hashable_iite;
    r_q       =
      Dequeue.create () ~initial_length:63;
    r_obj = None;
    r_fun_cnt = 0;
    r_unsat   = false;
  }

  let get_f ({r_ctx; r_fun_m; r_fun_cnt} as r)
      (Id.Box_arrow.Box id' as id) =
    let t = I.type_of_t id' in
    Hashtbl.find_or_add r_fun_m id
      ~default:(fun () ->
        let s = Printf.sprintf "f_%d" r_fun_cnt in
        r.r_fun_cnt <- r.r_fun_cnt + 1;
        S.new_f r_ctx s (Type.count_arrows t))

  let ivar_of_iid {r_ctx; r_ivar_m; r_iid_m} x =
    Hashtbl.find_or_add r_ivar_m x
      ~default:(fun () ->
        let v = S.new_ivar r_ctx mip_type_int in   
        Hashtbl.replace r_iid_m v x; v)

  let rvar_of_rid {r_ctx; r_rvar_m; r_rid_m} x =
    Hashtbl.find_or_add r_rvar_m x
      ~default:(fun () ->
	let v = S.new_ivar r_ctx mip_type_real in       
	Hashtbl.replace r_rid_m v x; v)

   let bvar_of_bid {r_ctx; r_bvar_m; r_bid_m} x =
    Hashtbl.find_or_add r_bvar_m x
      ~default:(fun () ->
        let v = S.new_bvar r_ctx in
        Hashtbl.replace r_bid_m v x; v)

  let iid_of_ivar {r_iid_m} = Hashtbl.find r_iid_m

  let bid_of_bvar {r_bid_m} = Hashtbl.find r_bid_m

  let rid_of_rvar {r_rid_m} = Hashtbl.find r_rid_m

  (* linearizing terms and formulas: utilities before we get into the
     mutually recursive part *)

  let snot = function
    | S_Pos x -> S_Neg x
    | S_Neg x -> S_Pos x

  let negate_isum =
    List.map ~f:(Tuple2.map1 ~f:Int63.neg)

  let negate_rsum = 
    List.map ~f:(Tuple2.map1 ~f:(Float.neg))

  (* linearizing terms and formulas: mutual recursion, because terms
     contain formulas and vice versa *)

  let rec iexpr_of_sum ({r_sum_m} as r) (l, o) =
    let l, o' =
      Hashtbl.find_or_add r_sum_m l
        ~default:(fun () ->
          let f (l, o) (c, t) =
            match ovar_of_flat_term_base r t with
            | Some v, x ->
              (c, v) :: l, Int63.(o + c * x)
            | None, x ->
              l, Int63.(o + c * x)
          and init = [], Int63.zero in
          List.fold_left ~init ~f l) in
    l, Int63.(o' + o)

(*  and iexpr_of_sum_real ({r_rsum_m} as r) (l, o) =
    let l, o' = 
      Hashtbl.find_or_add r_rsum_m l
	~default:(fun () ->
	  let f (l,o) (c,t) = 
	    match ovar_of_flat_term_base_real r t with
	      | Some v, x ->
		(c,v) :: l, Float.(o + c *x)
	      | None, x ->
		l, Float.(o + c * x)
	  and init = [], Float.zero in
	  List.fold_left ~init ~f l) in
    l, Float.(o' + o)
*)
  and iexpr_of_sum_mixed ({r_msum_m} as r) (l,o) =
    let l, o' =
      Hashtbl.find_or_add r_msum_m l
	~default:(fun () ->
	  let f (l, o) = function
	    | P.S_Int (c,t) -> (
	      let c' = Int63.to_float c in
	      match ovar_of_flat_term_base_mixed r t with
		| Some v, x -> 
		  (c' , v) :: l, Float.(o + c' * x)
		| None, x ->
		  l, Float.(o + c' * x))
	    | P.S_Real (c, t) -> (
	      match ovar_of_flat_term_base_mixed r t with
		| Some v, x -> 
		  (c , v) :: l, Float.(o + c * x)
		| None, x ->
		  l, Float.(o + c * x))
	  and init = [], Float.zero in
	  List.fold_left ~init ~f l) in
    l, Float.(o' + o)
      

  and iexpr_of_flat_term r = function
    | P.G_Sum s ->
      iexpr_of_sum r s
    | P.G_Base b ->
      (match ovar_of_flat_term_base r b with
      | Some v, x ->
        [Int63.one, v], x
      | None, x ->
        [], x)
    | P.G_SumM s -> raise (Unreachable.Exn _here_)

  and iexpr_of_flat_term_mixed r = function
    | P.G_SumM s -> iexpr_of_sum_mixed r s
    | P.G_Base b ->
     (match ovar_of_flat_term_base_mixed r b with
      | Some v, x ->
        [Float.(1.0), v], x
      | None, x ->
        [], x)
    | P.G_Sum s -> raise (Unreachable.Exn _here_)      

  and blast_le ?v ({r_ctx} as r) s =
    let l, o = iexpr_of_sum r s
    and v = match v with Some v -> v | _ -> S.new_bvar r_ctx in
    S.add_indicator r_ctx (S_Pos v)  l                (Int63.neg o);
    S.add_indicator r_ctx (S_Neg v)  (negate_isum l)  Int63.(o - one);
    S_Pos (Some v)

 (* and blast_le_real ?v ({r_ctx} as r) s =
    let l,o = iexpr_of_sum_real r s
    and v = match v with Some v -> v | _ -> S.new_bvar r_ctx in
    S.add_real_indicator r_ctx (S_Pos v) l (Float.neg o);
    S.add_real_indicator r_ctx (S_Neg v) (negate_rsum l) Float.(o - 1.0);
    S_Pos (Some v) 
 *)
  and blast_le_mixed ?v ({r_ctx} as r) s =
    let l,o = iexpr_of_sum_mixed r s
    and v = match v with Some v -> v | _ -> S.new_bvar r_ctx in
    S.add_real_indicator r_ctx (S_Pos v) l (Float.neg o);
    S.add_real_indicator r_ctx (S_Neg v) (negate_rsum l) Float.(o - 1.0);
    S_Pos (Some v)

(* add_indicator expects a list of pairs where the first component is an int. Then it casts int -> to float before passing it to scip. This function is almost identical but handles Float negation and invokes add_real_indicator, similar to the other one but expects floats as first projection*)
(*  and blast_eq_real ({r_ctx} as r) s =
    let l, o = iexpr_of_sum_rea r s in
    let l_neg = negate_rsum l in
    let b = S.new_bvar r_ctx in
    let b_lt = S_Pos (S.new_bvar r_ctx)
    and b_gt = S_Pos (S.new_bvar r_ctx)
    and b_eq = S_Pos b in
    S.add_real_indicator r_ctx b_eq l (Float.neg o);
    S.add_real_indicator r_ctx b_eq l_neg o;
    S.add_real_indicator r_ctx b_lt l Float.(neg o - 1.0);
    S.add_real_indicator r_ctx b_gt l_neg Float.(o - 1.0);
    S.add_clause r_ctx [b_eq; b_lt; b_eq];
    S_Pos (Some b) 
*)
 and blast_eq_mixed ({r_ctx} as r) s =
    let l, o = iexpr_of_sum_mixed r s in
    let l_neg = negate_rsum l in
    let b = S.new_bvar r_ctx in
    let b_lt = S_Pos (S.new_bvar r_ctx)
    and b_gt = S_Pos (S.new_bvar r_ctx)
    and b_eq = S_Pos b in
    S.add_real_indicator r_ctx b_eq l (Float.neg o);
    S.add_real_indicator r_ctx b_eq l_neg o;
    S.add_real_indicator r_ctx b_lt l Float.(neg o - 1.0);
    S.add_real_indicator r_ctx b_gt l_neg Float.(o - 1.0);
    S.add_clause r_ctx [b_eq; b_lt; b_eq];
    S_Pos (Some b) 

    
  and blast_eq ({r_ctx} as r) s =
    let l, o = iexpr_of_sum r s in
    let l_neg = negate_isum l in
    let b    = S.new_bvar r_ctx in
    let b_lt = S_Pos (S.new_bvar r_ctx)
    and b_gt = S_Pos (S.new_bvar r_ctx)
    and b_eq = S_Pos b in
    S.add_indicator r_ctx b_eq  l      (Int63.neg o);
    S.add_indicator r_ctx b_eq  l_neg  o;
    S.add_indicator r_ctx b_lt  l      Int63.(neg o - one);
    S.add_indicator r_ctx b_gt  l_neg  Int63.(o - one);
    S.add_clause r_ctx [b_eq; b_lt; b_gt];
    S_Pos (Some b)

(*Do I need a version for real numbers?*)
  and var_of_app ({r_ctx; r_call_m} as r) f_id l t =
    let f = get_f r f_id
    and l = List.map l ~f:(ovar_of_ibeither r)
    and default () = S.new_ivar r_ctx t in
    let v = Hashtbl.find_or_add r_call_m (f, l) ~default in
    S.add_call r_ctx (Some v, Int63.zero) f l;
    v

(* and var_of_app_real ({r_ctx; r_call_m} as r) f_id l t =
    let f = get_f r f_id
    and l = List.map l ~f:(ovar_of_ibeither r)
    and default () = S.new_ivar r_ctx t in
    let v = Hashtbl.find_or_add r_call_m (f, l) ~default in
    S.add_call_real r_ctx (Some v, Float.zero) f l;
    v
*)
  and blast_ite_branch ({r_ctx} as r) xv v e =
    let l, o = iexpr_of_flat_term r e in
    let l = (Int63.minus_one, v) :: l in
    S.add_indicator r_ctx xv  l                (Int63.neg o);
    S.add_indicator r_ctx xv  (negate_isum l)  o

  and ovar_of_ite ({r_ctx; r_ovar_of_iite_m} as r) ((g, s, t) as i) =
    let default () =
      match xvar_of_formula_doit r g with
      | S_Pos None ->
        ovar_of_term r s
      | S_Neg None ->
        ovar_of_term r t
      | S_Pos (Some bv) ->
        let v = S.new_ivar r_ctx mip_type_int in
        blast_ite_branch r (S_Pos bv) v s;
        blast_ite_branch r (S_Neg bv) v t;
        Some v, Int63.zero
      | S_Neg (Some bv) ->
        let v = S.new_ivar r_ctx mip_type_int in
        blast_ite_branch r (S_Neg bv) v s;
        blast_ite_branch r (S_Pos bv) v t;
        Some v, Int63.zero in
    Hashtbl.find_or_add r_ovar_of_iite_m i ~default

  and blast_ite_branch_mixed ({r_ctx} as r) xv v e =
    let l, o = iexpr_of_flat_term_mixed r e in
    let l = (Float.(-1.0), v) :: l in
    S.add_real_indicator r_ctx xv  l                (Float.neg o);
    S.add_real_indicator r_ctx xv  (negate_rsum l)  o

 (* and ovar_of_ite_real ({r_ctx; r_rovar_of_iite_m} as r) ((g,s,t) as i) = 
    let default () =
      match xvar_of_formula_doit r g with
      | S_Pos None ->
        ovar_of_term_mixed r s
      | S_Neg None ->
        ovar_of_term_mixed r t
      | S_Pos (Some bv) ->
        let v = S.new_ivar r_ctx mip_type_real in
        blast_ite_branch_real r (S_Pos bv) v s;
        blast_ite_branch_real r (S_Neg bv) v t;
        Some v, Float.zero
      | S_Neg (Some bv) ->
        let v = S.new_ivar r_ctx mip_type_real in
        blast_ite_branch_real r (S_Neg bv) v s;
        blast_ite_branch_real r (S_Pos bv) v t;
        Some v, Float.zero in
    Hashtbl.find_or_add r_rovar_of_iite_m i ~default
 *)

and ovar_of_ite_mixed ({r_ctx; r_rovar_of_iite_m} as r) ((g,s,t) as i) = 
    let default () =
      match xvar_of_formula_doit r g with
      | S_Pos None ->
        ovar_of_term_mixed r s
      | S_Neg None ->
        ovar_of_term_mixed r t
      | S_Pos (Some bv) ->
        let v = S.new_ivar r_ctx mip_type_real in
        blast_ite_branch_mixed r (S_Pos bv) v s;
        blast_ite_branch_mixed r (S_Neg bv) v t;
        Some v, Float.zero
      | S_Neg (Some bv) ->
        let v = S.new_ivar r_ctx mip_type_real in
        blast_ite_branch_mixed r (S_Neg bv) v s;
        blast_ite_branch_mixed r (S_Pos bv) v t;
        Some v, Float.zero in
    Hashtbl.find_or_add r_rovar_of_iite_m i ~default


  and ovar_of_flat_term_base r = function
    | P.B_IVar v ->
      Some (ivar_of_iid r v), Int63.zero
    | P.B_RVar v -> raise (Invalid_argument "Undefined case for ILP")
    | P.B_Formula g ->
      ovar_of_formula r g
    | P.B_App (f_id, l) ->
      Some (var_of_app r f_id l mip_type_int), Int63.zero
    | P.B_Ite i ->
      ovar_of_ite r i


(* Added case to process B_VarF. Can't use ovar_of_flat_term_base because manipulates Int offset*)
 (* and ovar_of_flat_term_base_real r = function
    | P.B_IVar v ->
      Some (ivar_of_iid r v), Float.zero
    | P.B_RVar v -> Some (rvar_of_rid r v), Float.zero 
    | P.B_Formula g ->
      ovar_of_formula_mixed r g
    | P.B_App (f_id, l) ->
      Some (var_of_app r f_id l mip_type_real), Float.zero
    | P.B_Ite i ->
    ovar_of_ite_mixed r i
 *)

  and ovar_of_flat_term_base_mixed r = function
    | P.B_IVar v  -> Some (ivar_of_iid r v), Float.zero
    | P.B_RVar v -> Some (rvar_of_rid r v), Float.zero
    | P.B_Formula g -> ovar_of_formula_mixed r g
    | P.B_App (f_id, l) -> Some (var_of_app r f_id l mip_type_real), Float.zero
    |P.B_Ite i -> ovar_of_ite_mixed r i
        
  and ovar_of_term ({r_ctx; r_var_of_sum_m} as r) = function
    | P.G_Base b ->
      ovar_of_flat_term_base r b
    | P.G_Sum s ->
      (match iexpr_of_sum r s with
      | [], o ->
        None, o
      | [c, x], o when Int63.(c = one) ->
        Some x, o
      | l, o ->
        let v =
          let default () =
            let v = S.new_ivar r_ctx mip_type_int in
            S.add_eq r_ctx ((Int63.minus_one, v) :: l) Int63.zero;
            v in
          Hashtbl.find_or_add r_var_of_sum_m l ~default in
        Some v, o)
    | P.G_SumM s -> raise (Failure "Invalid case mixed: ovar_of_flat_term_base_real")

and ovar_of_term_mixed ({r_ctx; r_rvar_of_rsum_m} as r) = function
    | P.G_Base b ->
      ovar_of_flat_term_base_mixed r b
    | P.G_SumM s ->
      (match iexpr_of_sum_mixed r s with
      | [], o ->
        None, o
      | [c, x], o when Float.(c = Float.(1.0)) ->
        Some x, o
      | l, o ->
        let v =
          let default () =
            let v = S.new_ivar r_ctx mip_type_real in
            S.add_real_eq r_ctx ((Float.(-1.0), v) :: l) Float.zero;
            v in
          Hashtbl.find_or_add r_rvar_of_rsum_m l ~default in
        Some v, o)
    | P.G_Sum s -> raise (Failure "Invalid case")   (* TODO ddd case for this *)
   


  and ovar_of_formula ({r_ctx} as r) g =
    match xvar_of_formula_doit r g with
    | S_Pos (Some v) ->
      Some (S.ivar_of_bvar v), Int63.zero
    | S_Pos None ->
      None, Int63.one
    | S_Neg v ->
      (let f v = S.ivar_of_bvar (S.negate_bvar r_ctx v) in
       Option.map v ~f), Int63.zero

(*
  and ovar_of_formula_real ({r_ctx} as r) g =   (*Remove *)
    match xvar_of_formula_doit r g with
      | S_Pos (Some v) ->
	Some (S.ivar_of_bvar v), Float.zero                  
      | S_Pos None -> 
	None, Float.zero
      | S_Neg v ->
	(let f v = S.ivar_of_bvar (S.negate_bvar r_ctx v) in
	 Option.map v ~f), Float.zero
  *)
 and ovar_of_formula_mixed ({r_ctx} as r) g =
    match xvar_of_formula_doit r g with
      | S_Pos (Some v) ->
	Some (S.ivar_of_bvar v), Float.zero                  
      | S_Pos None -> 
	None, Float.zero
      | S_Neg v ->
	(let f v = S.ivar_of_bvar (S.negate_bvar r_ctx v) in
	 Option.map v ~f), Float.zero


  and ovar_of_ibeither ({r_ctx} as r) = function
    | H_Int (P.G_Base b) ->
      ovar_of_flat_term_base r b
    | H_Int (P.G_Sum s) ->
      (match iexpr_of_sum r s with
      | [], o ->
        None, o
      | [c, x], o when Int63.(c = one) ->
        Some x, o
      | l, o ->
        let v = S.new_ivar r_ctx mip_type_int in
        S.add_eq r_ctx ((Int63.minus_one, v) :: l) (Int63.neg o);
        Some v, Int63.zero)
    | H_Bool g ->
      ovar_of_formula r g
    | H_Float (P.G_Base b) -> raise (Failure "Invalid case") (* TODO add case for this*)
    | H_Float (P.G_SumM s) -> raise (Failure "Invalid case") (*Add case*)
    | H_Float (P.G_Sum s)  -> raise (Failure "Check this case")
    | _ -> raise (Failure "Invalid case") (*we shouldn't fine H_Int G_SumM *)


  and blast_atom ({r_ctx} as r) = function
    | P.G_Base t, O'_Le ->
      blast_le r ([Int63.one, t], Int63.zero)
    | P.G_Sum s, O'_Le ->
      blast_le r s
    | P.G_Base t, O'_Eq ->
      blast_eq r ([Int63.one, t], Int63.zero)
    | P.G_Sum s, O'_Eq ->
      blast_eq r s
    | P.G_SumM s, O'_Le -> blast_le_mixed r s
    | P.G_SumM s, O'_Eq -> blast_eq_mixed r s 

  and blast_conjunction_map r acc = function
    | g :: tail ->
      (match xvar_of_formula_doit r g with
      | S_Pos (Some x) ->
        blast_conjunction_map r (S_Pos x :: acc) tail
      | S_Pos None ->
        blast_conjunction_map r acc tail
      | S_Neg (Some x) ->
        blast_conjunction_map r (S_Neg x :: acc) tail
      | S_Neg None ->
        None)
    | [] ->
      Some acc

  and blast_conjunction_reduce {r_ctx} l =
    match l with
    | [] ->
      xtrue
    | [S_Pos x] ->
      S_Pos (Some x)
    | [S_Neg x] ->
      S_Neg (Some x)
    | _ ->
      let rval = S.new_bvar r_ctx in
      (let f v = S.add_clause r_ctx [S_Neg rval; v] in
       List.iter l ~f);
      S.add_clause r_ctx (S_Pos rval :: List.map l ~f:snot);
      S_Pos (Some rval)

  and blast_conjunction r l =
    Option.value_map (blast_conjunction_map r [] l)
      ~f:(blast_conjunction_reduce r)
      ~default:xfalse

  and blast_formula r = function
    | P.U_Not _ | P.U_Ite (_, _, _) ->
      raise (Unreachable.Exn _here_)
    | P.U_Var v ->
      S_Pos (Some (bvar_of_bid r v))
    | P.U_App (f_id, l) ->
      S_Pos (Some
               (S.bvar_of_ivar
                  (var_of_app r f_id l mip_type_bool)))
    | P.U_Atom (t, o) ->
      blast_atom r (t, o)
    | P.U_And l ->
      blast_conjunction r l

  and xvar_of_formula_doit ({r_xvar_m} as r) = function
    | P.U_Not g ->
      snot (xvar_of_formula_doit r g)
    | P.U_Ite (q, g, h) ->
      xvar_of_formula_doit r (P.ff_ite q g h)
    | g ->
      let default () = blast_formula r g in
      Hashtbl.find_or_add r_xvar_m g ~default

  let assert_ivar_equal_constant {r_ctx} v c =
    S.add_eq r_ctx [Int63.one, v] c

  let assert_ivar_le_constant {r_ctx} v c =
    S.add_le r_ctx [Int63.one, v] c

  let assert_bvar_equal_constant {r_ctx} v c =
    let v = S.ivar_of_bvar v in
    S.add_eq r_ctx [Int63.one, v] c

  let finally_assert_unit ({r_ctx} as r) = function
    | S_Pos (Some v) ->
      assert_bvar_equal_constant r v Int63.one
    | S_Neg (Some v) ->
      assert_bvar_equal_constant r v Int63.zero
    | S_Pos None ->
      ()
    | S_Neg None ->
      r.r_unsat <- true

  let rec finally_assert_formula ({r_ctx} as r) = function
    | P.U_And l ->
      List.iter l ~f:(finally_assert_formula r)
    | P.U_Var v ->
      assert_bvar_equal_constant r (bvar_of_bid r v) Int63.one
    | P.U_App (f_id, l) ->
      let v = var_of_app r f_id l mip_type_bool in
      assert_ivar_equal_constant r v Int63.one
    | P.U_Atom (P.G_Sum s, O'_Le) ->
      let l, o = iexpr_of_sum r s in
      S.add_le r_ctx l (Int63.neg o)
    | P.U_Atom (P.G_Sum s, O'_Eq) ->
      let l, o = iexpr_of_sum r s in
      S.add_eq r_ctx l (Int63.neg o)
    | P.U_Atom (P.G_Base a, O'_Le) ->
      (match ovar_of_flat_term_base r a with
      | None, o when Int63.(o > zero) ->
        r.r_unsat <- true
      | None, _ ->
        ()
      | Some v, o ->
        assert_ivar_le_constant r v (Int63.neg o))
    | P.U_Atom (P.G_Base a, O'_Eq) ->
      (match ovar_of_flat_term_base r a with
      | None, o when Int63.(o = zero) ->
        ()
      | None, _ ->
        r.r_unsat <- true
      | Some v, o ->
        assert_ivar_equal_constant r v (Int63.neg o))
    | g ->
      finally_assert_unit r (xvar_of_formula_doit r g)

  let assert_formula {r_pre_ctx; r_q} g =
    Dequeue.enqueue_back r_q (P.flatten_formula r_pre_ctx g)

  let negate_bvar {r_ctx} v =
    S.negate_bvar r_ctx v

  let xvar_of_formula ({r_pre_ctx} as r) g =
    let g = P.flatten_formula r_pre_ctx g in
    lazy (xvar_of_formula_doit r g)

 
  let xvar_of_term ({r_pre_ctx} as r) m =
    let g = P.flatten_bool_term r_pre_ctx m in
    lazy (xvar_of_formula_doit r g)

  let ovar_of_term ({r_pre_ctx} as r) m =
    let m = P.flatten_int_term r_pre_ctx m in
    lazy (ovar_of_term r m)

  let bvar_of_id = bvar_of_bid

  let write_bg_ctx {r_ctx} =
    S.write_ctx r_ctx

  let bg_assert_all_cached ({r_q} as r) =
    Dequeue.iter r_q ~f:(finally_assert_formula r);
    Dequeue.clear r_q

  let solve ({r_ctx; r_obj} as r) =
    bg_assert_all_cached r;
    match r_obj, r.r_unsat with
    | _, true ->
      R_Unsat
    | Some o, false ->
      let l, _ = iexpr_of_flat_term r o in
      (match S.add_objective r_ctx l with
      | `Duplicate ->
        raise (Unreachable.Exn _here_)
      | `Ok ->
        S.solve r_ctx)
    | None, false ->
      S.solve r_ctx

  let solve_real ({r_ctx; r_obj} as r) =
    bg_assert_all_cached r;
    match r_obj, r.r_unsat with
    | _, true ->
      R_Unsat
    | Some o, false ->
      let l, _ = iexpr_of_flat_term_mixed r o in
      (match S.add_real_objective r_ctx l with
      | `Duplicate ->
        raise (Unreachable.Exn _here_)
      | `Ok ->
        S.solve r_ctx)
    | None, false ->
      S.solve r_ctx

  let add_objective ({r_obj; r_pre_ctx} as r) o =
    match r_obj with
    | None ->
      let m = P.flatten_int_term r_pre_ctx o in
      r.r_obj <- Some m; `Ok
    | Some _ ->
      `Duplicate

  let add_real_objective ({r_obj; r_pre_ctx} as r) o =
    match r_obj with
    | None ->
      let m = P.flatten_mixed_term r_pre_ctx o in
      r.r_obj <- Some m; `Ok
    | Some _ ->
      `Duplicate

  let add_real_objective2:
  type s . ctx -> (I.c, s) M.t ->  [`Duplicate | `Ok] =
    fun ({r_obj; r_pre_ctx} as r) o ->
      match r_obj with
	| None -> 
	  let m = (match M.type_of_t o ~f:I.type_of_t' with
	    | Type.Y_Int  -> P.flatten_int_term r_pre_ctx o
	    | Type.Y_Real -> P.flatten_mixed_term r_pre_ctx o
	    | _ -> raise (Unreachable.Exn _here_))
	  in   
	  r.r_obj <- Some m; `Ok
	| Some _ ->
	  `Duplicate


  let deref_int {r_ctx; r_ivar_m} id =
    Option.(Hashtbl.find r_ivar_m id >>= S.ideref r_ctx)

  let deref_bool {r_ctx; r_bvar_m} id =
    Option.(Hashtbl.find r_bvar_m id >>= S.bderef r_ctx)

  let deref_real {r_ctx; r_rvar_m} id =
    Option.(Hashtbl.find r_rvar_m id >>= S.rderef r_ctx)

 


end
