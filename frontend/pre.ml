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
    (term, term, formula) Terminology.irbeither

  (* Some of the definitions below look pedantic, but the
     corresponding compare_* functions are useful. *)

  and args =
    ibflat list

  and app =
    fun_id * args

  and sumt =
    Int63.t * term_base

  and mixed_sumt = 
     | S_Int of Int63.t * term_base
     | S_Real of Float.t * term_base
   
  and mixed_sumt2 = 
      (Int63.t, Float.t) ireither * mixed_term_base
    
  and sum =
    sumt list

  and mixed_sum =
    mixed_sumt list

  and mixed_sum2 = 
      mixed_sumt2 list

  and iite =
    formula * term * term

  and mixed_ite =
      mixed_formula * mixed_term * mixed_term

  and term_base =
  | B_IVar      of  (I.c, int) Id.t
  | B_RVar     of  (I.c, float) Id.t
  | B_Formula  of  formula
  | B_App      of  app
  | B_Ite      of  iite

  and mixed_term_base =
    | M_IVar of (I.c, int) Id.t
    | M_RVar of (I.c, float) Id.t
    | M_Formula of formula
    | M_App of app
    | M_Ite of mixed_ite

  and term =
  | G_Base   of  term_base
  | G_Sum    of  sum  Terminology.offset 
  | G_SumM   of  mixed_sum Terminology.roffset
  
  and mixed_term =
    | M_Base of mixed_term_base
    | M_Sum  of mixed_sum2 Terminology.roffset

  and bite = formula * formula * formula

  and conj = formula list

  and formula =
  | U_Var   of  (I.c, bool) Id.t
  | U_Atom  of  term * op'
  | U_Not   of  formula
  | U_And   of  conj
  | U_App   of  app
  | U_Ite   of  bite

  and mixed_bite = mixed_formula * mixed_formula * mixed_formula

  and mixed_conj = mixed_formula list

  and mixed_formula = 
    | MU_Var   of  (I.c, bool) Id.t
    | MU_Atom  of  mixed_term * op'
    | MU_Not   of  mixed_formula
    | MU_And   of  mixed_conj
    | MU_App   of  app
    | MU_Ite   of  mixed_bite


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

  let hashable_mixed_sum = {
    Hashtbl.Hashable.
    compare = compare_mixed_sum;
    hash = Hashtbl.hash;
    sexp_of_t = sexp_of_mixed_sum
  }

  let hashable_mixed_sum2 = {
    Hashtbl.Hashable.
    compare = compare_mixed_sum2;
    hash = Hashtbl.hash;
    sexp_of_t = sexp_of_mixed_sum2
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

  let hashable_mixed_ite = {
    Hashtbl.Hashable.
    compare = compare_mixed_ite;
    hash = Hashtbl.hash;
    sexp_of_t = sexp_of_mixed_ite
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

    s_sum_h         :  (sum, sum) Hashtbl.t;
    s_mixed_sum_h   :  (mixed_sum, mixed_sum) Hashtbl.t;   (* mixed int/float type*)
    s_mixed_sum2_h  :  (mixed_sum2, mixed_sum2) Hashtbl.t;
    s_args_h        :  (args, args) Hashtbl.t;
    s_iite_h        :  (iite, term_base) Hashtbl.t;
    s_mite_h        :  (mixed_ite, mixed_term_base) Hashtbl.t;
    s_bite_h        :  (bite, formula) Hashtbl.t;
    s_conj_h        :  (conj, formula) Hashtbl.t;
  
  }

  type ctx = {

    (* Tables to memorize top-level calls. This is to avoid translating
       the same terms/formulas multiple times. *)

    r_imemo_h  :  ((I.c, int) M.t, term) Hashtbl.Poly.t;
    r_rmemo_h  :  ((I.c, float) M.t, term) Hashtbl.Poly.t;
    r_bmemo_h  :  ((I.c, bool) M.t, formula) Hashtbl.Poly.t;
    r_fmemo_h  :  (I.c A.t Formula.t, formula) Hashtbl.Poly.t;

    r_sharing  :  sharing_ctx;
    
  }

  let make_sharing_ctx () = {
    s_sum_h        = Hashtbl.create () ~size:2048 ~hashable:hashable_sum;
    s_mixed_sum_h  = Hashtbl.create () ~size:2048 ~hashable:hashable_mixed_sum;
    s_mixed_sum2_h  = Hashtbl.create () ~size:2048 ~hashable:hashable_mixed_sum2;
    s_args_h       = Hashtbl.create () ~size:2048 ~hashable:hashable_args;
    s_iite_h       = Hashtbl.create () ~size:2048 ~hashable:hashable_iite;
    s_mite_h       = Hashtbl.create () ~size:2048 ~hashable:hashable_mixed_ite;
    s_bite_h       = Hashtbl.create () ~size:2048 ~hashable:hashable_bite;
    s_conj_h       = Hashtbl.create () ~size:2048 ~hashable:hashable_conj;
  }

  let make_ctx () = {
    r_imemo_h  = Hashtbl.Poly.create () ~size:4096;
    r_rmemo_h  = Hashtbl.Poly.create () ~size:4096; 
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


(*Deduplication for G_Sum-like lists*)
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



(*This won't be necessary anymore *)

  let dedup_real_sum l =
    let sorter (n1,v1) (n2, v2) = if compare_term_base v1 v2 = 0
				  then Float.to_int(Float.(n1 - n2))
				  else compare_term_base v1 v2 in			 
    let l = List.sort ~cmp:sorter l in
    let rec loop ~acc = function
      | [] -> acc
      | hd :: [] -> hd :: acc
      | (c1, m1) :: (c2, m2) :: d when compare_term_base m1 m2 = 0 ->
	      loop ~acc ((Float.(c1 +. c2), m1) :: d)
      | (c, m) :: d when c = Float.zero -> loop ~acc d
      | a :: d -> loop ~acc:(a :: acc) d in
    loop ~acc:[] l



(*
Input: summ list
The function deduplicates the list so that only one summ element remains for each variabl by combining the coeffcients of the multiple ocurrences of summ for a variable. Particularly when a variable appears with a real coefficient and with an integer coefficient, a single S_Real element is computed by converting int coefficients to real coeffficients.

A new sorting criteria is defined so that S_Int and S_Real for any term_base remain in continuous positions.
*)

  let dedup_mixed_sum l =
    let comp t t' = match t, t' with
                       | S_Int(c, b), S_Real(c', b') -> 
			 let dif = compare_term_base b b' in 
			 if dif = 0
			 then (Float.to_int(Float.((Int63.to_float c) - c')))
			 else dif
		       | S_Real(c', b'), S_Int(c, b) -> 
			 let dif = compare_term_base b b' in 
			 if dif = 0
			 then (Float.to_int(Float.(c' - (Int63.to_float c))))
			 else dif
		       | _, _ -> compare_mixed_sumt t t' in
    let l = List.sort ~cmp:comp l in
    let rec loop ~acc = function
      | [] -> acc
      | hd :: [] -> hd :: acc
      | (S_Int (c1, m1)) :: (S_Int (c2, m2)) :: d when compare_term_base m1 m2 = 0 ->
	loop ~acc ((S_Int (Int63.(c1 + c2), m1)) :: d)
      | (S_Real (c1, m1)) :: (S_Real (c2, m2)) :: d when compare_term_base m1 m2 = 0 ->
	loop ~acc ((S_Real (Float.(c1 +. c2), m1)) :: d)
      | (S_Real (c1, m1)) :: (S_Int (c2, m2)) :: d when compare_term_base m1 m2 = 0 ->
	loop ~acc ((S_Real (Float.(c1 + (Int63.to_float(c2))), m1)) :: d)
      | (S_Int (c1, m1)) :: (S_Real (c2, m2)) :: d when compare_term_base m1 m2 = 0 ->
	loop ~acc ((S_Real (Float.(c2 + (Int63.to_float(c1))), m1)) :: d)
      | (S_Int (c, m))  :: d when c = Int63.zero -> loop ~acc d
      | (S_Real (c, m)) :: d when c = Float.zero -> loop ~acc d
      | a :: d -> loop ~acc:(a :: acc) d in
    loop ~acc:[] l

  let rec make_real k d x =
    match d with
      | [] -> [], Int63.to_float(x)
      | (c,t) :: tl -> let new_tl, new_x = make_real k tl x in
			 (k *. (Int63.to_float c), t) :: new_tl, new_x 
  
  (*Convert a G_Sum-like list to a G_SumM-like list by applying a float k multiplier to the coefficients. As k<>1.0 is a float, all terms have to be converted to S_Real. If k = 1.0 then there's no nedd to convert the coefficients to float, thus the terms are converted to S_Int*)

  let rec make_mixed k l =
    match l with
      | [] -> []
      | (c, v) :: xs when k <> Float.(1.0) -> 
	(S_Real (Float.(k * (Int63.to_float c)), v)) :: (make_mixed k xs)
      | (c,v) :: xs -> 
	(S_Int (c,v)) :: (make_mixed k xs)

   let rec make_mixed2 k l =
    match l with
      | [] -> []
      | (c, v) :: xs when k <> Float.(1.0) ->
	(W_Real Float.(k * (Int63.to_float c)), v) :: (make_mixed2 k xs)
      | (c, v) :: xs ->
	(W_Int c, v) :: (make_mixed2 k xs)


 let make_sum {r_sharing = {s_sum_h}} l o =
    let l = dedup_sum l in
    Hashtbl.find_or_add s_sum_h l ~default:(fun () -> l), o

  let make_mixed_sum {r_sharing = {s_mixed_sum_h}} l ro = 
    let l = dedup_mixed_sum l in
    Hashtbl.find_or_add s_mixed_sum_h l ~default:(fun()->l), ro
 
  let make_args {r_sharing = {s_args_h}} l =
    Hashtbl.find_or_add s_args_h l ~default:(fun () -> l)

  let make_iite {r_sharing = {s_iite_h}} a b c =
    let i = a, b, c in
    Hashtbl.find_or_add s_iite_h i ~default:(fun () -> B_Ite i)

  let make_mixed_ite {r_sharing = {s_mite_h}} a b c =
    let i = a, b, c in
    Hashtbl.find_or_add s_mite_h i ~default:(fun () -> M_Ite i)

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

  let rec mixed_negate = function
    | MU_Not MU_Not g ->
      mixed_negate g
    | MU_Not g ->
      g
    | g ->
      MU_Not g


(*This function expects to receive G_Sum or G_Base. We shouldn't have comparison between G_Sum and G_SumM*)
   let equal_modulo_offset a b =
    match a, b with
    | G_Base b1, G_Base b2 ->
      Option.some_if
        (compare_term_base b1 b2 = 0)
        Int63.zero
    | G_Sum ([c, b1], o), G_Base b2 ->
      Option.some_if
        (c = Int63.one && compare_term_base b1 b2 = 0)
        o
    | G_Base b2, G_Sum ([c, b1], o) ->
      Option.some_if
        (c = Int63.one && compare_term_base b1 b2 = 0)
        (Int63.neg o)
    | G_Sum (s1, o1), G_Sum (s2, o2) ->
      Option.some_if
        (compare_sum s1 s2 = 0)
        Int63.(o1 - o2)
    | _ ->
      None

   let equal_mixed_modulo_offset (a : mixed_term) (b : mixed_term) =
     match a, b with
       | M_Base b1, M_Base b2 ->
	 Option.some_if
           (compare_mixed_term_base b1 b2 = 0)
           Float.zero
       | M_Sum ([W_Int c, b1], o), M_Base b2 ->
	 Option.some_if
           (c = Int63.one && compare_mixed_term_base b1 b2 = 0)
           o
       | M_Sum ([W_Real c, b1], o), M_Base b2 ->
	 Option.some_if
           (c = Float.(1.0) && compare_mixed_term_base b1 b2 = 0)
           o
       | M_Base b2, M_Sum ([W_Real c, b1], o) ->
	 Option.some_if
           (c = Float.(1.0) && compare_mixed_term_base b1 b2 = 0)
           (Float.neg o)
       | M_Base b2, M_Sum ([W_Int c, b1], o) ->
	 Option.some_if
           (c = Int63.one && compare_mixed_term_base b1 b2 = 0)
           (Float.neg o)
       | M_Sum (s1, o1), M_Sum (s2, o2) ->
	 Option.some_if
           (compare_mixed_sum2 s1 s2 = 0)
           Float.(o1 - o2)
       | _ ->
	 None


(*Similar to the above but here we expect G_Base and G_SumM*)
 let equal_modulo_real_offset a b =
    match a, b with
    | G_Base b1, G_Base b2 ->
      Option.some_if
        (compare_term_base b1 b2 = 0)
        Float.zero
    | G_SumM ([S_Int(c, b)], ro), G_Base b' ->
      Option.some_if
	(c = Int63.one && compare_term_base b b' = 0)
	ro
    | G_Base b', G_SumM ([S_Int(c, b)], ro) ->
      Option.some_if
	(c = Int63.one && compare_term_base b b' = 0)
	(Float.neg(ro))
    | G_SumM ([S_Real(c, b)], ro), G_Base b' ->
      Option.some_if
	(c = Float.(1.0) && compare_term_base b b' = 0)
        ro
    | G_Base b', G_SumM ([S_Real(c, b)], ro) ->
      Option.some_if
	(c = Float.(1.0) && compare_term_base b b' = 0)
	(Float.neg(ro))
    | G_SumM (s, ro), G_SumM (s', ro') ->
      Option.some_if
	(compare_mixed_sum s s' = 0)
	(Float.(ro - ro'))
    | _ -> None

  let sum_of_term = function
    | G_Sum s ->
      s
    | G_Base b ->
      [Int63.one, b], Int63.zero
    | G_SumM s -> raise (Failure "Undefined case for G_SumM") 

  let sum_of_mixed_term = function
    | G_SumM s ->
      s
    | G_Base b ->
      [S_Real ((Float.(1.0), b))], Float.zero
    | G_Sum (l,o) -> 
      make_mixed (Float.(1.0)) l, (Int63.to_float o)

  let sum_of_mixed_term' (s : mixed_term) = 
    match s with
      | M_Base b ->
	[W_Real Float.(1.0), b], Float.zero
      | M_Sum s ->
	s
      



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

  let is_mixed_bounding = function
    | MU_Not (MU_Atom (s, O'_Eq)) :: d ->
      List.for_all d
        ~f:(function
        | MU_Not (MU_Atom (s2, O'_Eq)) ->
          Option.is_some (equal_mixed_modulo_offset s s2)
        | _ ->
          false)
    | _ ->
      false


  let get_bounding l =
    if not (is_bounding l) then
      None
    else
      let s = match l with
 	| U_Not (U_Atom (G_Sum (s, _), _)) :: _ ->
	  (make_mixed (Float.(1.0)) s)
	| U_Not (U_Atom (G_SumM (s, _), _)) :: _ ->
	  s
        | U_Not (U_Atom (G_Base b, _)) :: _ ->
          [S_Real (Float.(1.0), b)]
        | _ ->
          raise (Unreachable.Exn _here_)
      and l =
        let f acc = function
          | U_Not (U_Atom (G_Base _, _)) ->
            Float.zero :: acc
 	  | U_Not (U_Atom (G_Sum (_, d), _)) ->
	    (Int63.to_float d) :: acc
	  | U_Not (U_Atom (G_SumM (_,d), _)) ->
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

let get_mixed_bounding l =
    if not (is_mixed_bounding l) then
      None
    else
      let s = match l with
 	| MU_Not (MU_Atom (M_Sum (s, _), _)) :: _ ->
	  s
        | MU_Not (MU_Atom (M_Base b, _)) :: _ ->
          [W_Real (Float.(1.0)), b]
        | _ ->
          raise (Unreachable.Exn _here_)
      and l =
        let f acc = function
          | MU_Not (MU_Atom (M_Base _, _)) ->
            Float.zero :: acc
 	  | MU_Not (MU_Atom (M_Sum (_,d), _)) ->
	    d :: acc
          | _ ->
            acc
        and init = []
        and cmp = Float.compare in
        List.sort (List.fold_left l ~init ~f) ~cmp in
      let first = List.hd_exn l
      and last = List.last_exn l
      and length = Float.of_int (List.length l) in
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

let maybe_resolve_mixed 
     r
    (g : mixed_formula) 
    (h : mixed_formula) =
    let ret f g h = Some (f, mixed_negate g, mixed_negate h) in
    match g, h with
    | MU_Not (MU_And [g1; g2]), MU_Not (MU_And [h1; h2]) ->
      (let h1' = mixed_negate h1 and h2' = mixed_negate h2 in
       if compare_mixed_formula g1 h1' = 0 then
         ret g1 g2 h2
       else if compare_mixed_formula g1 h2' = 0 then
         ret g1 g2 h1
       else if compare_mixed_formula g2 h1' = 0 then
         ret g2 g1 h2
       else if compare_mixed_formula g2 h2' = 0 then
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

  and inline_term r (d, x) k = function
    | G_Base b ->
      (k, b) :: d, x
    | G_Sum (l, o) -> 
      List.rev_map_append l d ~f:(Tuple2.map1 ~f:(Int63.( * ) k)), Int63.(x + o * k)
    | _ -> raise (Failure "inline integer term: unexpected sum case")

  and inline_mixed_term 
    (r :ctx)
    (d, xr)
    (k : float)
    (s : mixed_term) = 
      match s with 
	| M_Base b -> ((W_Real k), b) :: d, xr
	| M_Sum (l, ro) -> 
	  let apply = (function
	    | W_Int c, v when Float.(k <> 1.0) ->
	      W_Real (Float.((Int63.to_float c) * k)), v
	    | W_Int c, v ->
	      W_Int c, v
	    | W_Real c, v ->
	      W_Real (c *. k), v) in
	  List.rev_map_append l d ~f:apply, Float.(xr + ro * k)

  
and inline_term_real r (d, xr) k = function
    | G_Base b ->  (S_Real (k, b)) :: d, xr
    | G_SumM (l, ro) ->
      let apply = function
	| S_Int (c, v) when Float.(k <> 1.0) ->  S_Real (Float.((Int63.to_float c) * k), v)
	| S_Int (c, v) -> S_Int(c, v)
        | S_Real (c, v) -> S_Real (Float.(c * k), v) in
      List.rev_map_append l d ~f:apply, Float.(xr + ro * k)
    | _ -> raise (Failure "inline real term: unexpected sum case")

 and flatten_int_term_aux ({r_sharing = {s_sum_h}} as r) = function
    | M.M_Var v ->
      G_Base (B_IVar v)
    | M.M_Ite (c, s, t) ->
      let c = flatten_formula r c
      and s = flatten_int_term r s
      and t = flatten_int_term r t in
      G_Base (make_iite r c s t)
    | M.M_App (f, t) ->
      G_Base (B_App (flatten_args r [flatten_term r t] f))
    | M.M_Int _ | M.M_Sum (_, _) | M.M_Prod (_, _) as t ->
      let d, x = [], Int63.zero in
      let d, x = flatten_int_term_sum r (d, x) Int63.one t in
      G_Sum (make_sum r d x)

and flatten_int_term_sum r (d, x) k (t : (_, int) M.t) =
    match t with
    | M.M_Var v ->
       (k, B_IVar v) :: d, x
    | M.M_Int i ->
      d, Int63.(x + k * i)
    | M.M_App (f, t) ->
      let a = flatten_args r [flatten_term r t] f in
       (k, B_App a) :: d, x
    | M.M_Sum (s, t) ->
      let d, x = flatten_int_term_sum r (d, x) k s in
      flatten_int_term_sum r (d, x) k t
    | M.M_Prod (k2, t) ->
      flatten_int_term_sum r (d, x) Int63.(k * k2) t
    | M.M_Ite (c, s, t) ->
      let c = flatten_formula r c
      and s = flatten_int_term r s 
      and t = flatten_int_term r t in
      (match equal_modulo_offset s t with
      | Some o ->
        let d, x = inline_term r (d, x) k t in
         (Int63.(k * o), B_Formula c) :: d, x
      | None ->
        (k, make_iite r c s t) :: d, x)


  and flatten_mixed_term_aux ({r_sharing={s_mixed_sum_h}} as r) = function
    | M.M_Var v ->
      G_Base (B_RVar v)
    | M.M_ROI x -> G_SumM (sum_of_mixed_term (flatten_int_term r x)) 
    | M.M_RIte (c, s, t) -> 
      let c = flatten_formula r c
      and s = flatten_mixed_term r s
      and t = flatten_mixed_term r t in
      G_Base (make_iite r c s t)
    | M.M_App (f, t) ->
      G_Base (B_App (flatten_args r [flatten_term r t] f))
    | M.M_Real _ | M.M_RSum (_, _) | M.M_RProd (_, _) as t->
      let d, xr = [], Float.zero in
      let d, xr = flatten_mixed_term_sum r (d, xr) (1.0) t in
      G_SumM (make_mixed_sum r d xr)
    

  (*and flatten_mixed_term_sum2 r (d, xr) k = function
    | M.M_Var v -> (W_Real k, M_RVar v) :: d, xr
    | M.M_Real i -> d, Float.(xr + k * i)
    | M.M_ROI i -> let d_aux, xi_aux = flatten_int_term_sum r ([],Int63.zero) Int63.one i in
		   let xr_new = Float.((Int63.to_float xi_aux) * k + xr) in
		   (List.append d (make_mixed2 k d_aux)), xr_new
    | M.M_App (f, t) ->
      let a = flatten_args r [flatten_term r t] f in
      (W_Real k, M_App a) :: d, xr
    | M.M_RSum (s, t) ->
      let d, xr = flatten_mixed_term_sum2 r (d, xr) k s in
      flatten_mixed_term_sum2 r (d, xr) k t
    | M.M_RProd(k', t) ->
      flatten_mixed_term_sum2 r (d, xr) Float.(k *. k') t
    | M.M_RIte (c, s, t) ->
      let c = flatten_formula r c
      and s = flatten_mixed_term r s 
      and t = flatten_mixed_term r t in
      (match equal_mixed_modulo_offset s t with
	| Some o ->
	  let d, xr = inline_mixed_term r (d, xr) k t in  
	  (W_Real Float.(k *. o), M_Formula c) :: d, xr
	| None ->
	  (W_Real k, make_mixed_ite r c s t) :: d, xr)
  *)

 and flatten_mixed_term_sum r (d, xr) k = function
    | M.M_Var v -> (S_Real (k, B_RVar v)) :: d, xr
    | M.M_Real i -> d, Float.(xr +. k *. i)
    | M.M_ROI i -> let d_aux, xi_aux = flatten_int_term_sum r ([],Int63.zero) Int63.one i in
		   let xr_new = Float.((Int63.to_float xi_aux) * k + xr) in
		   (List.append d (make_mixed k d_aux)), xr_new
    | M.M_App (f, t) ->
      let a = flatten_args r [flatten_term r t] f in
       (S_Real (k, B_App a)) :: d, xr
    | M.M_RSum(s, t) -> 
      let d, xr = flatten_mixed_term_sum r (d, xr) k s in
      flatten_mixed_term_sum r (d, xr) k t
    | M.M_RProd(k', t) ->
      flatten_mixed_term_sum r (d, xr) Float.(k *. k') t
    | M.M_RIte(c,s,t) ->
      let c = flatten_formula r c
      and s = flatten_mixed_term r s 
      and t = flatten_mixed_term r t in
      (match equal_modulo_real_offset s t with
	|Some o ->
	  let d, xr = inline_term_real r (d, xr) k t in  
	  (S_Real (Float.(k *. o), B_Formula c)) :: d, xr
	|None ->
	  (S_Real (k, make_iite r c s t)) :: d, xr)

 
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

  and flatten_mixed_term ({r_rmemo_h} as r) s =
    Hashtbl.find_or_add r_rmemo_h s
      ~default:(fun () -> flatten_mixed_term_aux r s) 

  and flatten_int_term ({r_imemo_h} as r) s =
    Hashtbl.find_or_add r_imemo_h s
      ~default:(fun () -> flatten_int_term_aux r s)

  and flatten_term :
  type s . ctx -> (I.c, s) M.t -> ibflat =
    fun r t ->
      match M.type_of_t t with
      | Type.Y_Int ->
        D_Int (flatten_int_term r t)
      | Type.Y_Real ->
        D_Real (flatten_mixed_term r t) 
      | Type.Y_Bool ->
        D_Bool (flatten_bool_term r t)
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
                [negate (U_Atom (G_SumM (s, Float.(Float.(1.0) - lb)), O'_Le));
                 U_Atom (G_SumM (s, Float.neg ub), O'_Le)])
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
        U_Atom (G_Sum (make_sum r l o), og)
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
    | Formula.F_Atom (A.A_LeR t) ->
      U_Atom (flatten_mixed_term r t, O'_MLe)
    | Formula.F_Atom (A.A_Eq t) ->
      U_Atom (flatten_int_term r t, O'_Eq)
    | Formula.F_Atom (A.A_EqR t) ->
      U_Atom (flatten_mixed_term r t, O'_MEq) 
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
