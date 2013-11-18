open Core.Std
open Terminology
open Logic

(* TODO: investigate why type_conv (or camlp4 itself?) breaks module
   signatures, like:

   module type Pre_step = sig
     type ctx
     type formula
     val transform : ctx -> formula -> formula
   end

*)

module Make (I : Id.Accessors) = struct

  type fun_id = I.c Id.Box_arrow.t 
  with compare, sexp_of

  let fun_id_of_sexp x =
    raise (Unreachable.Exn _here_)

  type ibflat =
    (term, formula) Terminology.ifbeither (*Should change this type to be (float, bool)??*)

  (* Some of the definitions below look pedantic, but the
     corresponding compare_* functions are useful. *)

  and args =
    ibflat list

  and app =
    fun_id * args

  and sumt =
    Int63.t * term_base

  and new_sumt = 
    | IntC   of Int63.t * term_base
    | FloatC of Float.t * term_base

  and new_sum = new_sumt list

  and sumtf = 
    Float.t * term_base

  and sum =
    sumt list

  and sumf = 
    sumtf list

  and iite =
    formula * term * term

  and term_base =
  | B_Var      of  (I.c, int) Id.t
  | B_VarF     of  (I.c, float) Id.t
  | B_Formula  of  formula
  | B_App      of  app
  | B_Ite      of  iite

  and term =
  | G_Base  of  term_base
 (* | G_Sum   of  new_sum Terminology.float_offset *)
  | G_Sum   of  sum  Terminology.offset 
  | G_SumF  of  sumf Terminology.float_offset  

  and bite = formula * formula * formula

  and conj = formula list

  and formula =
  | U_Var   of  (I.c, bool) Id.t
  | U_Atom  of  term * op'
  | U_Not   of  formula
  | U_And   of  conj
  | U_App   of  app
  | U_Ite   of  bite

  with compare, sexp_of

  (* To use the functorial interface to [Core.Std.Hashtbl], we would
     have to implement t_of_sexp functions. In the presence of GADTs,
     this is not easy. *)

  let hashable_sum = {
    Hashtbl.Hashable.
    compare = compare_sum;
    hash = Hashtbl.hash;
    sexp_of_t = sexp_of_sum
  }

  let hashable_sumf = {
    Hashtbl.Hashable.
    compare = compare_sumf;
    hash = Hashtbl.hash;
    sexp_of_t = sexp_of_sumf
  }

 let hashable_new_sum = {
    Hashtbl.Hashable.
    compare = compare_new_sum;
    hash = Hashtbl.hash;
    sexp_of_t = sexp_of_new_sum
  }

  let hashable_args = {
    Hashtbl.Hashable.
    compare = compare_args;
    hash = Hashtbl.hash;
    sexp_of_t = sexp_of_args
  }

  let hashable_iite = {
    Hashtbl.Hashable.
    compare = compare_iite;
    hash = Hashtbl.hash;
    sexp_of_t = sexp_of_iite
  }

  let hashable_bite = {
    Hashtbl.Hashable.
    compare = compare_bite;
    hash = Hashtbl.hash;
    sexp_of_t = sexp_of_bite
  }

  let hashable_conj = {
    Hashtbl.Hashable.
    compare = compare_conj;
    hash = Hashtbl.hash;
    sexp_of_t = sexp_of_conj
  }

  let hashable_formula = {
    Hashtbl.Hashable.
    compare = compare_formula;
    hash = Hashtbl.hash;
    sexp_of_t = sexp_of_formula
  }

  let true_formula = U_And []
    
  let false_formula = U_Not true_formula

  let dummy_formula = true_formula

  type sharing_ctx = {

    (* Tables that enforce sharing subterms / subformulas. Not every
       single sub{term,formula} is shared, but we don't have to go
       very deep before we find shared parts. *)

    s_sum_h    :  (sum, sum) Hashtbl.t;
    s_sumf_h   :  (sumf, sumf) Hashtbl.t;
    s_new_sum_h:  (new_sum, new_sum) Hashtbl.t;
    s_args_h   :  (args, args) Hashtbl.t;
    s_iite_h   :  (iite, term_base) Hashtbl.t;
    s_bite_h   :  (bite, formula) Hashtbl.t;
    s_conj_h   :  (conj, formula) Hashtbl.t;
  
  }

  type ctx = {

    (* Tables to memorize top-level calls. This is to avoid translating
       the same terms/formulas multiple times. *)

    r_imemo_h  :  ((I.c, int) M.t, term) Hashtbl.Poly.t;
    r_flmemo_h :  ((I.c, float) M.t, term) Hashtbl.Poly.t;
    r_bmemo_h  :  ((I.c, bool) M.t, formula) Hashtbl.Poly.t;
    r_fmemo_h  :  (I.c A.t Formula.t, formula) Hashtbl.Poly.t;

    r_sharing  :  sharing_ctx;
    
  }

  let make_sharing_ctx () = {
    s_sum_h   = Hashtbl.create () ~size:2048 ~hashable:hashable_sum;
    s_sumf_h  = Hashtbl.create () ~size:2048 ~hashable:hashable_sumf;
    s_new_sum_h = Hashtbl.create ()  ~size:2048 ~hashable:hashable_new_sum;
    s_args_h  = Hashtbl.create () ~size:2048 ~hashable:hashable_args;
    s_iite_h  = Hashtbl.create () ~size:2048 ~hashable:hashable_iite;
    s_bite_h  = Hashtbl.create () ~size:2048 ~hashable:hashable_bite;
    s_conj_h  = Hashtbl.create () ~size:2048 ~hashable:hashable_conj;
  }

  let make_ctx () = {
    r_imemo_h  = Hashtbl.Poly.create () ~size:4096;
    r_flmemo_h = Hashtbl.Poly.create () ~size:4096; 
    r_bmemo_h  = Hashtbl.Poly.create () ~size:4096;
    r_fmemo_h  = Hashtbl.Poly.create () ~size:4096;
    r_sharing  = make_sharing_ctx ();
  }

  (* we will expand-out ITE right before blasting *)
  let ff_ite q g h =
    let ff_not = function U_Not g -> g | g -> U_Not g in
    let ff_or a b = U_Not (U_And [ff_not a; ff_not b]) in
    U_And [ff_or (ff_not q) g; ff_or q h]

  let sum_negate (l, x) =
    List.map l ~f:(Tuple2.map1 ~f:Int63.neg), Int63.neg x

  (* flatten terms and formulas; SCC impractical to break 
  let dedup_sum l =
    let l = List.sort ~cmp:compare_sumt l in
    let rec loop ~acc = function
      | [] ->
        acc
      | hd :: [] ->
        hd :: acc
      | (c1, m1) :: (c2, m2) :: d when compare_term_base m1 m2 = 0 ->
        loop ~acc ((Int63.(c1 + c2), m1) :: d)
      | (c, m) :: d when c = Int63.zero ->
        loop ~acc d
      | a :: d ->
        loop ~acc:(a :: acc) d in
    loop ~acc:[] l
  *)

  let dedup_sum l =
    let l = List.sort ~cmp:compare_new_sumt l in
    let rec loop ~acc = function
      | [] ->
        acc
      | hd :: [] ->
        hd :: acc
      | (IntC (c1, m1)) :: (IntC (c2, m2)) :: d when compare_term_base m1 m2 = 0 ->
        loop ~acc ((IntC (Int63.(c1 + c2), m1)) :: d)
      | (FloatC (c1, m1)) :: (FloatC (c2, m2)) :: d when compare_term_base m1 m2 = 0 ->
        loop ~acc ((FloatC (Float.(c1 +. c2), m1)) :: d)
      | (IntC (c, m)) :: d when c = Int63.zero ->
        loop ~acc d
      | (FloatC (c, m)) :: d when c = Float.zero ->
        loop ~acc d
      | a :: d ->
        loop ~acc:(a :: acc) d in
    loop ~acc:[] l

  let dedup_sumf l =
    let l = List.sort ~cmp:compare_sumtf l in
    let rec loop ~acc = function
      | [] -> acc
      | hd :: [] -> hd :: acc
      | (c1, m1) :: (c2, m2) :: d when compare_term_base m1 m2 = 0 ->
	      loop ~acc ((Float.(c1 +. c2), m1) :: d)
      | (c, m) :: d when c = Float.zero -> loop ~acc d
      | a :: d -> loop ~acc:(a :: acc) d in
    loop ~acc:[] l


  let make_sum {r_sharing = {s_new_sum_h}} l o =
    let l = dedup_sum l in
    Hashtbl.find_or_add s_new_sum_h l ~default:(fun () -> l), o

  let make_sumf {r_sharing = {s_sumf_h}} l o =
    let l = dedup_sumf l in
    Hashtbl.find_or_add s_sumf_h l ~default:(fun()->l), o

  
  let make_args {r_sharing = {s_args_h}} l =
    Hashtbl.find_or_add s_args_h l ~default:(fun () -> l)

  let make_iite {r_sharing = {s_iite_h}} a b c =
    let i = a, b, c in
    Hashtbl.find_or_add s_iite_h i ~default:(fun () -> B_Ite i)

  let make_bite {r_sharing = {s_bite_h}} a b c =
    let i = a, b, c in
    Hashtbl.find_or_add s_bite_h i ~default:(fun () -> U_Ite i)

  let rec elim_not_not = function
    | U_Not U_Not g ->
      elim_not_not g
    | g ->
      g

  let rec compare_formula_abs x y =
    match x, y with
    | U_Not U_Not x, _ ->
      compare_formula_abs (elim_not_not x) y
    | _, U_Not U_Not y ->
      compare_formula_abs x (elim_not_not y)
    | U_Not x, U_Not y ->
      compare_formula x y
    | U_Not x, y ->
      let i = compare_formula x y in
      if i = 0 then -1 else i
    | x, U_Not y ->
      let i = compare_formula x y in
      if i = 0 then 1 else i
    | _, _ ->
      compare_formula x y

  let rec negate = function
    | U_Not U_Not g ->
      negate g
    | U_Not g ->
      g
    | g ->
      U_Not g

 (* let equal_modulo_offset a b =
    match a, b with
    | G_Base b1, G_Base b2 ->
      Option.some_if
        (compare_term_base b1 b2 = 0)
        Float.zero
    | G_Sum ([t], o), G_Base b2 ->
      (match t with 
	| IntC(c, b1)   ->  Option.some_if
                             (c = Int63.one && compare_term_base b1 b2 = 0)
                             o
	| FloatC(c, b1) -> Option.some_if
                             (c = Float.(1.0) && compare_term_base b1 b2 = 0)
                             o )
    | G_Base b2, G_Sum ([t], o) ->
      (match t with 
	| IntC(c, b1)   ->  Option.some_if
                             (c = Int63.one && compare_term_base b1 b2 = 0)
                             (Float.neg o)
	| FloatC(c, b1) -> Option.some_if
                             (c = Float.(1.0) && compare_term_base b1 b2 = 0)
                             (Float.neg o))       
    | G_Sum (s1, o1), G_Sum (s2, o2) ->
      Option.some_if
        (compare_new_sum s1 s2 = 0)
        Float.(o1 -. o2)
    | _ -> None *)

 let equal_modulo_offset a b =
    match a, b with
    | G_Base b1, G_Base b2 ->
      Option.some_if
        (compare_term_base b1 b2 = 0)
        Float.zero
    | G_SumF ([c, b1], o), G_Base b2 ->
          Option.some_if
                 (c = Float.(1.0) && compare_term_base b1 b2 = 0)
                  o
    | G_Base b2, G_SumF ([c, b1], o) ->
     	   Option.some_if
                 (c = Float.(1.0) && compare_term_base b1 b2 = 0)
                 (Float.neg o)  
    | G_SumF (s1, o1), G_SumF (s2, o2) ->
      Option.some_if
        (compare_sumf s1 s2 = 0)
        Float.(o1 -. o2)
    | _ -> None

 (* 
  let equal_modulo_offset_float a b =
    match a, b with
    | G_Base b1, G_Base b2 ->
      Option.some_if
        (compare_term_base b1 b2 = 0)
        Float.zero
    | G_Sum ([c, b1], o), G_Base b2 ->
      Option.some_if
        (c = Int63.one && compare_term_base b1 b2 = 0)
        (Int63.to_float o)
    | G_Base b2, G_Sum ([c, b1], o) ->
      Option.some_if
        (c = Int63.one && compare_term_base b1 b2 = 0)
        (Float.neg (Int63.to_float o))
    | G_Sum (s1, o1), G_Sum (s2, o2) ->
      Option.some_if
        (compare_sum s1 s2 = 0)
        (Int63.to_float(Int63.(o1 - o2)))
    | G_SumF ([c, b1], o), G_Base b2 ->
      Option.some_if
        (c = (1.0) && compare_term_base b1 b2 = 0)
        o
    | G_Base b2, G_SumF ([c, b1], o) ->
      Option.some_if
        (c = (1.0) && compare_term_base b1 b2 = 0)
        (Float.neg o)
    | G_SumF (s1, o1), G_SumF (s2, o2) ->
      Option.some_if
        (compare_sumf s1 s2 = 0)
        Float.(o1 -. o2)
    | _ ->
      None
 *)

  let sum_of_term = function
   (* | G_Sum (s,o) ->
      let rec convert_to_sumf = function
	| [] -> []
	| (i,t) :: l -> (Int63.to_float i, t)::(convert_to_sumf l) in
      (convert_to_sumf s, (Int63.to_float o))  *)
    | G_SumF s ->
      s
    | G_Base b ->
      [(Float.(1.0), b)], Float.zero
    | _ -> [], Float.zero  (* Este caso hay que borrarlo, queda provisorio por G_Sum *)

  let is_bounding = function
    | U_Not (U_Atom (s, O'_Eq)) :: d ->
      List.for_all d
        ~f:(function
        | U_Not (U_Atom (s2, O'_Eq)) ->
          Option.is_some (equal_modulo_offset s s2)
        | _ ->
          false)
    | _ ->
      false

  let get_bounding l =
    if not (is_bounding l) then
      None
    else
      let s = match l with
        | U_Not (U_Atom (G_SumF (s, _), _)) :: _ ->
          s
        | U_Not (U_Atom (G_Base b, _)) :: _ ->
          [(Float.(1.0), b)]
        | _ ->
          raise (Unreachable.Exn _here_)
      and l =
        let f acc = function
          | U_Not (U_Atom (G_Base _, _)) ->
            Float.zero :: acc
          | U_Not (U_Atom (G_SumF (_, d), _)) ->
            d :: acc
          | _ ->
            acc
        and init = []
        and cmp = Float.compare in
        List.sort (List.fold_left l ~init ~f) ~cmp in
      let first = List.hd_exn l
      and last = List.last_exn l
      and length = Float.of_int(List.length l) in
      let lb = Float.neg last and ub = Float.neg first in
      assert(Float.(lb <= ub));
      Some (s, lb, ub, ub = Float.(lb + length - (1.0)))

  let maybe_resolve r g h =
    let ret f g h = Some (f, negate g, negate h) in
    match g, h with
    | U_Not (U_And [g1; g2]), U_Not (U_And [h1; h2]) ->
      (let h1' = negate h1 and h2' = negate h2 in
       if compare_formula g1 h1' = 0 then
         ret g1 g2 h2
       else if compare_formula g1 h2' = 0 then
         ret g1 g2 h1
       else if compare_formula g2 h1' = 0 then
         ret g2 g1 h2
       else if compare_formula g2 h2' = 0 then
         ret g2 g1 h1
       else
         None)
    | _, _ ->
      None

  let rec flatten_args :
  type s t . ctx -> ibflat list -> (I.c, s -> t) M.t -> app =
    fun r acc -> function
    | M.M_App (f, t) ->
      flatten_args r (flatten_term r t :: acc) f
    | M.M_Var v ->
      Id.Box_arrow.Box v, make_args r (List.rev acc)
(*
  and inline_term r (d, x) k = function
    | G_Base b ->
      (k, b) :: d, x
    | G_Sum (l, o) ->  
      List.rev_map_append l d ~f:(fun t -> match t with
	                                    | IntC (c,n)   -> Float.((Int63.to_float c) *. k ), n
					    | FloatC (c,n) -> Float.(c *. k), n ),
      Float.(x +. o *. k) 
    | _ -> [], Float.zero   (*revisar*)
*)
  and inline_term r (d, x) k = function
    | G_Base b -> (k, b) :: d, x
    | G_SumF (l, o)  -> 
      List.rev_map_append l d ~f:(Tuple2.map1 ~f:(Float.( * ) k)),
      Float.(x +. o *. k)
    | _ -> [], Float.zero
  

  and flatten_int_term_aux ({r_sharing = {s_sum_h}} as r) = function
    | M.M_Var v ->
      G_Base (B_Var v)
    | M.M_Ite (c, s, t) ->
      let c = flatten_formula r c
      and s = flatten_int_term r s
      and t = flatten_int_term r t in
      G_Base (make_iite r c s t)
    | M.M_App (f, t) ->
      G_Base (B_App (flatten_args r [flatten_term r t] f))
    | M.M_Int _ | M.M_Sum (_, _) | M.M_Prod (_, _) as t ->
      let d, x = [], Float.zero in               (*Convedra que sea float?*)
      let d, x = flatten_int_term_sum r (d, x) (Float.(1.0)) t in
      G_SumF (make_sumf r d x)

  and flatten_int_term_sum r (d, x) k (t : (_, int) M.t) =   (*Cambio todas las operaciones sobre x para que sean tipo float *)
    match t with
    | M.M_Var v ->
      (k, B_Var v) :: d, x
    | M.M_Int i ->
      d, Float.(x +. k *. Int63.to_float(i))
    | M.M_App (f, t) ->
      let a = flatten_args r [flatten_term r t] f in
      (k, B_App a) :: d, x
    | M.M_Sum (s, t) ->
      let d, x = flatten_int_term_sum r (d, x) k s in
      flatten_int_term_sum r (d, x) k t
    | M.M_Prod (k2, t) ->
      flatten_int_term_sum r (d, x) Float.(k *. Int63.to_float(k2)) t
    | M.M_Ite (c, s, t) ->
      let c = flatten_formula r c
      and s = flatten_int_term r s 
      and t = flatten_int_term r t in
      (match equal_modulo_offset s t with
      | Some o ->
        let d, x = inline_term r (d, x) k t in
        (Float.(k *. o), B_Formula c) :: d, x
      | None ->
        (k, make_iite r c s t) :: d, x) 

  and flatten_float_term_aux ({r_sharing={s_sumf_h}} as r) = function
    | M.M_Var v ->
      G_Base (B_VarF v)
    | M.M_FIte (c, s, t) -> 
      let c = flatten_formula r c
      and s = flatten_float_term r s
      and t = flatten_float_term r t in
      G_Base (make_iite r c s t)
    | M.M_App (f, t) ->
      G_Base (B_App (flatten_args r [flatten_term r t] f))
    | M.M_Float _ | M.M_FSum (_, _) | M.M_FProd (_, _) as t->
      let d, x = [], Float.zero in
      let d, x = flatten_float_term_sum r (d,x) (1.0) t in
      G_SumF (make_sumf r d x)
    
  and flatten_float_term_sum r (d,x) k = function
    | M.M_Var v -> (k, B_VarF v) :: d,x
   (* | M.M_Int i -> d, Float.(x +. k *.(Float.of_int64 i))*)
    | M.M_Float i -> d, Float.(x +. k *. i)
    | M.M_App (f, t) ->
      let a = flatten_args r [flatten_term r t] f in
      (k, B_App a) :: d, x
   (* | M.M_Sum (s, t) ->
      let d, x = flatten_arithmetic_term_sum r (d, x) k s in
      flatten_arithmetic_term_sum r (d, x) k t  *)
    | M.M_FSum(s, t) -> 
      let d, x = flatten_float_term_sum r (d, x) k s in
      flatten_float_term_sum r (d, x) k t
  (*  | M.M_Prod(k2, t) ->  
      flatten_arithmetic_term_sum r (d, x) Float.(k *. k2) t *)
    | M.M_FProd(k2, t) ->
      flatten_float_term_sum r (d, x) Float.(k *. k2) t
    | M.M_FIte(c,s,t) ->
      let c = flatten_formula r c
      and s = flatten_float_term r s 
      and t = flatten_float_term r t in
      (match equal_modulo_offset s t with
	|Some o ->
	  let d, x = inline_term r (d, x) k t in  (*TODO *)
	  (Float.(k *. o), B_Formula c) :: d, x
	|None ->
	  (k, make_iite r c s t) :: d, x)
 
  and flatten_bool_term_aux r = function
    | M.M_Var v ->
      U_Var v
    | M.M_Bool g ->
      flatten_formula r g
    | M.M_App (f, t)  ->
      let l = flatten_args r [flatten_term r t] f in
      U_App l

  and flatten_bool_term ({r_bmemo_h} as r) s =
    Hashtbl.find_or_add r_bmemo_h s
      ~default:(fun () -> flatten_bool_term_aux r s)

  and flatten_float_term ({r_flmemo_h} as r) s =
    Hashtbl.find_or_add r_flmemo_h s
      ~default:(fun () -> flatten_float_term_aux r s) 

  and flatten_int_term ({r_imemo_h} as r) s =
    Hashtbl.find_or_add r_imemo_h s
      ~default:(fun () -> flatten_int_term_aux r s)

  and flatten_term :
  type s . ctx -> (I.c, s) M.t -> ibflat =
    fun r t ->
      match M.type_of_t t ~f:I.type_of_t' with
      | Type.Y_Int ->
        H_Int (flatten_int_term r t)
      | Type.Y_Float ->
        H_Float (flatten_float_term r t) 
      | Type.Y_Bool ->
        H_Bool (flatten_bool_term r t)
      | _ ->
        (* not meant for functions *)
        raise (Unreachable.Exn _here_)

  and make_conj ({r_sharing = {s_conj_h}} as r) l =
    let ret l =
      let default () = U_And l in
      Hashtbl.find_or_add s_conj_h l ~default in
    let rec f acc = function
      | a :: U_Not ad :: dd
      | U_Not a :: ad :: dd when compare_formula a ad = 0 ->
        false_formula
      | a :: ((ad :: dd) as d) when compare_formula a ad = 0 ->
        f acc d
      | a :: ((ad :: dd) as d) ->
        (match maybe_resolve r a ad with
        | Some (q, g, h) ->
          f (make_bite_wrapper r q g h :: acc) dd
        | None ->
          f (a :: acc) d)
      | a :: d ->
        f (a :: acc) d
      | [] ->
        (let acc = List.rev acc in
         match get_bounding acc with
         | Some (s, lb, ub, true) ->
           negate
             (ret
                [negate (U_Atom (G_SumF (s, Float.(Float.(1.0) - lb)), O'_Le));
                 U_Atom (G_SumF (s, Float.neg ub), O'_Le)])
         | Some (s, lb, ub, false) ->
           ret acc
         | None ->
           ret acc) in
    f [] (List.sort l ~cmp:compare_formula_abs)

  and flatten_conjunction r d = function
    | Formula.F_True ->
      d
    | Formula.F_And (g, h) ->
      let d = flatten_conjunction r d g in
      flatten_conjunction r d h
    | g ->
      flatten_formula r g :: d

  and make_bite_wrapper r q g h =
    match g, h with
    | U_Atom (sg, og), U_Atom (sh, oh) when compare_op' og oh = 0 ->
      (match equal_modulo_offset sg sh with
      | Some k ->
        let l, o = sum_of_term sh in
        let l = (k, B_Formula q) :: l in
        U_Atom (G_SumF (make_sumf r l o), og)
      | None ->
        make_bite r q g h)
    | _ ->
      make_bite r q g h
  
  and flatten_formula_aux r = function
    | Formula.F_True ->
      true_formula
    | Formula.F_Atom (A.A_Bool t) ->
      flatten_bool_term r t
    | Formula.F_Atom (A.A_Le t) ->
      U_Atom (flatten_int_term r t, O'_Le)
    | Formula.F_Atom (A.A_LeF t) ->
      U_Atom (flatten_float_term r t, O'_Le)
    | Formula.F_Atom (A.A_Eq t) ->
      U_Atom (flatten_int_term r t, O'_Eq)
    | Formula.F_Atom (A.A_EqF t) ->
      U_Atom (flatten_float_term r t, O'_Eq) 
    | Formula.F_Not g ->
      negate (flatten_formula r g)
    | Formula.F_Ite (q, g, h) ->
      let q = flatten_formula r q
      and g = flatten_formula r g
      and h = flatten_formula r h in
      make_bite_wrapper r q g h
    | Formula.F_And (_, _) as g ->
      make_conj r (flatten_conjunction r [] g)

  and flatten_formula_dbg ({r_fmemo_h} as r) g =
    let rval =
      Hashtbl.find_or_add r_fmemo_h g
        ~default:(fun () -> flatten_formula_aux r g) in
    Sexplib.Sexp.output_hum Pervasives.stdout (sexp_of_formula rval);
    print_newline ();
    rval

  and flatten_formula ({r_fmemo_h} as r) g =
    Hashtbl.find_or_add r_fmemo_h g
      ~default:(fun () -> flatten_formula_aux r g)

  module Step : sig
    type ctx
    val rewrite : ctx -> formula -> formula
  end = struct
    type ctx = sharing_ctx
    let rewrite r g = g
  end

end
