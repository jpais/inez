open Core.Std
open Terminology
open Lang_abstract

module Make (I : Lang_ids.Accessors) = struct

  type fun_id = I.c Lang_ids.Box_arrow.t 
  with compare, sexp_of

  let fun_id_of_sexp x =
    raise (Unreachable.Exn _here_)

  type ibflat =
    (term, formula) Terminology.ibeither

  (* Some of the definitions below look pedantic, but the
     corresponding compare_* functions are useful. *)

  and args =
    ibflat list

  and app =
    fun_id * args

  and sumt =
    Int63.t * term_base

  and sum =
    sumt list

  and iite =
    formula * term * term

  and term_base =
  | B_Var   of  (I.c, int) Lang_ids.t
  | B_App   of  app
  | B_Ite   of  iite

  and term =
  | G_Base  of  term_base
  | G_Sum   of  sum Terminology.offset

  and bite = formula * formula * formula

  and conj = formula list

  and formula =
  | U_Var   of  (I.c, bool) Lang_ids.t
  | U_Atom  of  term * op'
  | U_Not   of  formula
  | U_And   of  conj
  | U_App   of  app
  | U_Ite   of  bite

  with compare, sexp_of

  module Sum = struct
    module T = struct
      type t = sum
      let compare = compare_sum
      let hash = Hashtbl.hash
      let sexp_of_t = sexp_of_sum
      let t_of_sexp _ = raise (Unreachable.Exn _here_)
    end
    include T
    include Hashable.Make(T)
  end

  module Args = struct
    module T = struct
      type t = args
      let compare = compare_args
      let hash = Hashtbl.hash
      let sexp_of_t = sexp_of_args
      let t_of_sexp _ = raise (Unreachable.Exn _here_)
    end
    include T
    include Hashable.Make(T)
  end

  module Iite = struct
    module T = struct
      type t = iite
      let compare = compare_iite
      let hash = Hashtbl.hash
      let sexp_of_t = sexp_of_iite
      let t_of_sexp _ = raise (Unreachable.Exn _here_)
    end
    include T
    include Hashable.Make(T)
  end

  module Bite = struct
    module T = struct
      type t = bite
      let compare = compare_bite
      let hash = Hashtbl.hash
      let sexp_of_t = sexp_of_bite
      let t_of_sexp _ = raise (Unreachable.Exn _here_)
    end
    include T
    include Hashable.Make(T)
  end

  module Conj = struct
    module T = struct
      type t = conj
      let compare = compare_conj
      let hash = Hashtbl.hash
      let sexp_of_t = sexp_of_conj
      let t_of_sexp _ = raise (Unreachable.Exn _here_)
    end
    include T
    include Hashable.Make(T)
  end

  let true_formula = U_And []
  
  let false_formula = U_Not true_formula

  let dummy_formula = true_formula

  type ctx = {

    (* Tables to memoize top-level calls. This is to avoid translating
       the same terms/formulas multiple times. *)

    r_imemo_h  :  ((I.c, int) M.t, term) Hashtbl.Poly.t;
    r_bmemo_h  :  ((I.c, bool) M.t, formula) Hashtbl.Poly.t;
    r_fmemo_h  :  (I.c A.t Formula.t, formula) Hashtbl.Poly.t;

    (* Tables that enforce sharing subterms / subformulas. Not every
       single sub{term,formula} is shared, but we don't have to go
       very deep before we find shared parts. *)
    
    r_sum_h    :  sum Sum.Table.t;
    r_args_h   :  args Args.Table.t;
    r_iite_h   :  term_base Iite.Table.t;
    r_bite_h   :  formula Bite.Table.t;
    r_conj_h   :  formula Conj.Table.t;
    
  }

  let make_ctx () = {
    r_imemo_h = Hashtbl.Poly.create () ~size:4096;
    r_bmemo_h = Hashtbl.Poly.create () ~size:4096;
    r_fmemo_h = Hashtbl.Poly.create () ~size:4096;
    r_sum_h = Sum.Table.create () ~size:2048;
    r_args_h = Args.Table.create () ~size:2048;
    r_iite_h = Iite.Table.create () ~size:2048;
    r_bite_h = Bite.Table.create () ~size:2048;
    r_conj_h = Conj.Table.create () ~size:2048;
  }

  (* we will expand-out ITE right before blasting *)
  let ff_ite q g h =
    let ff_not = function U_Not g -> g | g -> U_Not g in
    let ff_or a b = U_Not (U_And [ff_not a; ff_not b]) in
    U_And [ff_or (ff_not q) g; ff_or q h]

  let sum_negate (l, x) =
    List.map l ~f:(Tuple.T2.map1 ~f:Int63.neg), Int63.neg x

  (* flatten terms and formulas; SCC impractical to break *)
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

  let make_sum {r_sum_h} l o =
    let l = dedup_sum l in
    Hashtbl.find_or_add r_sum_h l ~default:(fun () -> l), o

  let make_args {r_args_h} l =
    Hashtbl.find_or_add r_args_h l ~default:(fun () -> l)

  let make_iite {r_iite_h} a b c =
    let i = a, b, c in
    Hashtbl.find_or_add r_iite_h i ~default:(fun () -> B_Ite i)

  let make_bite {r_bite_h} a b c =
    let i = a, b, c in
    Hashtbl.find_or_add r_bite_h i ~default:(fun () -> U_Ite i)

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

  let equal_modulo_offset a b =
    match a, b with
    | G_Base b1, G_Base b2 ->
      compare b1 b2 = 0
    | G_Sum ([c, b1], _), G_Base b2 when c = Int63.one ->
      compare b1 b2 = 0
    | G_Base b1, G_Sum ([c, b2], _) when c = Int63.one ->
      compare b1 b2 = 0
    | G_Sum (s1, _), G_Sum (s2, _) ->
      (* [phys_equal s1 s2] should suffice *)
      compare s1 s2 = 0
    | _ ->
      false

  let is_bounding = function
    | U_Not (U_Atom (s, O'_Eq)) :: d ->
      List.for_all d
        ~f:(function
        | U_Not (U_Atom (s2, O'_Eq)) ->
          equal_modulo_offset s s2
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
          s
        | U_Not (U_Atom (G_Base b, _)) :: _ ->
          [Int63.one, b]
        | _ ->
          raise (Unreachable.Exn _here_)
      and l =
        let f acc = function
          | U_Not (U_Atom (G_Base _, _)) ->
            Int63.zero :: acc
          | U_Not (U_Atom (G_Sum (_, d), _)) ->
            d :: acc
          | _ ->
            acc
        and init = []
        and cmp = Int63.compare in
        List.sort (List.fold_left l ~init ~f) ~cmp in
      let first = List.hd_exn l
      and last = List.last_exn l
      and length = Int63.of_int_exn (List.length l) in
      let lb = Int63.neg last and ub = Int63.neg first in
      assert(Int63.(lb <= ub));
      Some (s, lb, ub, ub = Int63.(lb + length - one))

  let make_conj {r_conj_h} l =
    let ret l =
      let default () = U_And l in
      Hashtbl.find_or_add r_conj_h l ~default in
    let rec f acc = function
      | a :: U_Not ad :: dd
      | U_Not a :: ad :: dd when compare_formula a ad = 0 ->
        false_formula
      | a :: ((ad :: dd) as d) when compare_formula a ad = 0 ->
        f acc d
      | a :: d ->
        f (a :: acc) d
      | [] ->
        (let acc = List.rev acc in
         match get_bounding acc with
         | Some (s, lb, ub, true) ->
           negate
             (ret
                [negate (U_Atom (G_Sum (s, Int63.(one - lb)), O'_Le));
                 U_Atom (G_Sum (s, Int63.neg ub), O'_Le)])
         | Some (s, lb, ub, false) ->
           ret acc
         | None ->
           ret acc) in
    f [] (List.sort l ~cmp:compare_formula_abs)

(*
  let make_conj {r_conj_h} l =
  let default () = U_And l in
  Hashtbl.find_or_add r_conj_h l ~default
*)

  let rec flatten_args :
  type s t . ctx -> ibflat list -> (I.c, s -> t) M.t -> app =
    fun r acc -> function
    | M.M_App (f, t) ->
      flatten_args r (flatten_term r t :: acc) f
    | M.M_Var v ->
      Lang_ids.Box_arrow.Box v, make_args r (List.rev acc)

  and flatten_int_term_sum r (d, x) k (t : (_, int) M.t) =
    match t with
    | M.M_Var v ->
      (k, B_Var v) :: d, x
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
      (k, make_iite r c s t) :: d, x

  and flatten_int_term_aux ({r_sum_h} as r) = function
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
      let d, x = [], Int63.zero in
      let d, x = flatten_int_term_sum r (d, x) Int63.one t in
      G_Sum (make_sum r d x)

  and flatten_int_term ({r_imemo_h} as r) s =
    Hashtbl.find_or_add r_imemo_h s
      ~default:(fun () -> flatten_int_term_aux r s)

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

  and flatten_term :
  type s . ctx -> (I.c, s) M.t -> ibflat =
    fun r t ->
      match M.type_of_t t ~f:I.type_of_t' with
      | Lang_types.Y_Int ->
        H_Int (flatten_int_term r t)
      | Lang_types.Y_Bool ->
        H_Bool (flatten_bool_term r t)
      | _ ->
        (* not meant for functions *)
        raise (Unreachable.Exn _here_)
          
  and flatten_conjunction r d = function
    | Formula.F_True ->
      d
    | Formula.F_And (g, h) ->
      let d = flatten_conjunction r d g in
      flatten_conjunction r d h
    | g ->
      flatten_formula r g :: d
        
  and flatten_formula_aux r = function
    | Formula.F_True ->
      true_formula
    | Formula.F_Atom (A.A_Bool t) ->
      flatten_bool_term r t
    | Formula.F_Atom (A.A_Le t) ->
      U_Atom (flatten_int_term r t, O'_Le)
    | Formula.F_Atom (A.A_Eq t) ->
      U_Atom (flatten_int_term r t, O'_Eq)
    | Formula.F_Not g ->
      negate (flatten_formula r g)
    | Formula.F_Ite (q, g, h) ->
      make_bite r
        (flatten_formula r q)
        (flatten_formula r g)
        (flatten_formula r h)
    | Formula.F_And (_, _) as g ->
      make_conj r (flatten_conjunction r [] g)

  and flatten_formula_dbg ({r_fmemo_h} as r) g =
    let g =
      Hashtbl.find_or_add r_fmemo_h g
        ~default:(fun () -> flatten_formula_aux r g) in
    Sexplib.Sexp.output_hum Pervasives.stdout (sexp_of_formula g);
    print_newline ();
    g

  and flatten_formula ({r_fmemo_h} as r) g =
    Hashtbl.find_or_add r_fmemo_h g
      ~default:(fun () -> flatten_formula_aux r g)

end