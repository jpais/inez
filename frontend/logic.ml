 open Core.Std
open Terminology
open Logic_intf

module Make_term (T : Core.T.T1) :

  (Term_with_ops with type 'i atom = 'i T.t) =

struct

  type 'i atom = 'i T.t

  type ('i, 'q) t =
  | M_Bool  :  'i atom Formula.t ->
    ('i, bool) t
  | M_Int   :  Core.Std.Int63.t ->
    ('i, int) t
  | M_Real : Core.Std.Float.t ->
    ('i, float) t
  | M_ROI : ('i, int) t -> ('i, float) t
  | M_Sum   : ('i, int) t * ('i, int) t ->
    ('i, int) t
  | M_RSum  :  ('i, float) t * ('i,float) t ->
    ('i, float) t
  | M_Prod  :  Core.Std.Int63.t * ('i, int) t ->
    ('i, int) t
  | M_RProd :  Core.Std.Float.t * ('i, float) t -> 
    ('i, float) t
  | M_Ite   :  'i atom Formula.t * ('i, int) t * ('i, int) t ->
    ('i, int) t
  | M_RIte  :  'i atom Formula.t * ('i, float) t * ('i, float) t ->
    ('i, float) t
  | M_Var   :  ('i, 's) Id.t ->
    ('i, 's) t
  | M_App   :  ('i, 'r -> 's) t * ('i, 'r) t ->
    ('i, 's) t

  let zero = M_Int Int63.zero

  let zeror = M_Real Float.zero

  let one = M_Int Int63.one

  let roi (x : ('i, int) t) = (M_ROI x : ('i, float) t)

  let of_int63 x = M_Int x

  let rec type_of_t :
  type s . ('i, s) t -> s Type.t =
    function
    | M_Bool _ ->
      Type.Y_Bool
    | M_Int _ ->
      Type.Y_Int
   	| M_Real  _ ->
      Type.Y_Real
   	| M_ROI _ -> 
      Type.Y_Real
    | M_Sum (_, _) ->
      Type.Y_Int
    | M_RSum (_,_) ->
      Type.Y_Real
    | M_Prod (_, _) ->
      Type.Y_Int
    | M_RProd (_,_) ->
	  Type.Y_Real
    | M_Ite (_, _, _) ->
      Type.Y_Int
    | M_RIte (_,_,_) ->
	  Type.Y_Real
    | M_Var id ->
      Id.type_of_t id
    | M_App (a, b) ->
      let t_a = type_of_t a
      and t_b = type_of_t b in
      Type.t_of_app t_a t_b

  let is_int :
  type s . ('i, s) t -> bool =
    fun m ->
      match type_of_t m with
      | Type.Y_Int ->
        true
      | _ ->
        false

  let is_bool :
  type s . ('i, s) t -> bool =
    fun m ->
      match type_of_t m with
      | Type.Y_Bool ->
        true
      | _ ->
        false

  let is_real :
  type s . ('i, s) t -> bool =
    fun m ->
      match type_of_t m with
      | Type.Y_Real ->
        true
      | _ ->
        false
        

  (* FIXME : definitely not the right place for this *)
  let rec fun_id_of_app :
  type r . ('i, r) t ->  'i Id.Box_arrow.t option =
    function
    | M_App (M_Var id, _) ->
      Some (Id.Box_arrow.Box id)
    | M_App (f, _) ->
      fun_id_of_app f
    | _ ->
      None

  let ( + ) a b =
    match a, b with
    | M_Int x, M_Int y ->
      M_Int Int63.(x + y)
    | M_Int x, _ when x = Int63.zero ->
      b
    | _, M_Int x when x = Int63.zero ->
      a
    | _ ->
      M_Sum (a, b)

  let ( +. ) a b =
    match a, b with
    | M_Real x, M_Real y              -> M_Real (x +. y)
    | M_Real x, _ when x = Float.zero -> b
    | _, M_Real x when x = Float.zero -> a
    | _                               -> M_RSum (a, b)


  let ( * ) c a =
    if c = Int63.zero then
      M_Int Int63.zero
    else
      M_Prod (c, a)

  let ( *. ) c a =
    if c = Float.zero then
      zeror
    else 
      M_RProd (c, a)
  
  let ( - ) a b =
    match a, b with
    | M_Int x, M_Int y ->
      M_Int (Int63.(-) x y)
    | M_Int x, _ when x = Int63.zero ->
      Int63.minus_one * b
    | _, M_Int x when x = Int63.zero ->
      a
    | _ ->
      a + (Int63.minus_one * b)

  let ( -. ) a b =
    match a, b with
    | M_Real x, M_Real y              -> M_Real ((-.) x y)
    | M_Real x, _ when x = Float.zero -> (-1.0) *. b
    | _, M_Real x when x = Float.zero -> a
    | _                               -> a +. ((-1.0) *. b)


  let ( ~- ) a =
    zero - a

  let ( ~-. ) a =
    zeror -. a

  let sum l ~f =
    let f acc x = acc + f x
    and init = zero in
    List.fold_left l ~init ~f
    
  let sumr l ~f =
    let f acc x = acc +. f x
    and init = zeror in
    List.fold_left l ~init ~f

  let rec fold :
  type s . ('i, s) t ->
    init:'a ->
    f:('a -> 'i T.t Formula.t -> 'a) -> 'a =
    fun m ~init ~f ->
      match m with
      | M_Int _ ->
        init
      | M_Real _ ->
	    init 
      | M_Var _ ->
        init
      | M_Bool b ->
        f init b
      | M_ROI x ->
        fold x ~init ~f
      | M_Sum (a, b) ->
        fold b ~init:(fold a ~init ~f) ~f
      | M_RSum (a, b) ->
	    fold b ~init:(fold a ~init ~f) ~f
      | M_Prod (_, a) ->
        fold a ~init ~f
      | M_RProd (_, a) ->
        fold a ~init ~f
      | M_Ite (q, a, b) ->
        let init = f init q in
        let init = fold a ~init ~f in
        fold b ~init ~f
      | M_RIte (q, a, b) ->
	    let init = f init q in
	    let init = fold a ~init ~f in
	    fold b ~init ~f
      | M_App (a, b) ->
        let init = fold a ~init ~f in
        fold b ~init ~f

  let rec fold_sum_terms_impl :
  type s . ('i, int) t ->
    factor   : Int63.t ->
    init     : 'a ->
    f        : ('a -> Int63.t -> ('i, int) t -> 'a) ->
    'a =
    fun m ~factor ~init ~f ->
      match m with
      | M_Sum (a, b) ->
        let init = fold_sum_terms_impl a ~factor ~init ~f in
        fold_sum_terms_impl b ~factor ~init ~f
      | M_Prod (c, a) ->
        if Int63.(c = zero) then
          init
        else
          let factor = Int63.(c * factor) in
          fold_sum_terms_impl a ~factor ~init ~f
      | _ ->
        f init factor m

  let rec fold_sum_terms m ~factor ~init ~f ~f_offset =
    (let f (acc, offset) c m =
       match m with
       | M_Int x ->
         acc, Int63.(offset + c * x)
       | _ ->
         f acc c m, offset in
     fold_sum_terms_impl m ~factor ~init:(init, Int63.zero) ~f) |>
        Tuple.T2.uncurry f_offset 

end

module rec M : (Term_with_ops with type 'i atom = 'i A.t) =
  Make_term(A)

and A : (Atom with type ('i, 's) term_plug := ('i, 's) M.t) = A

(* conversions between terms *)

module Make_term_conv (M1 : Term) (M2 : Term_with_ops) = struct

  open M2

  (* TODO : pass around polarity, for formulas of the form
     Formula.F_Atom (M1.M_Bool g) . In other cases, `Both is precise,
     i.e., it does not over-approximate. *)


  let rec map :
  type s . ('c1, s) M1.t ->
    f:('c1 M1.atom ->
       polarity:[ `Both | `Negative | `Positive ] ->
       'c2 M2.atom) ->
    fv:(('c1, 'c2) Id.id_mapper) ->
    ('c2, s) t =
    let polarity = `Both in
    fun s ~f ~fv ->
      match s with
      | M1.M_Bool g ->
        M_Bool (Formula.map g ~polarity ~f)
      | M1.M_Int i ->
        M_Int i
      | M1.M_Real i -> M_Real i
      | M1.M_ROI x -> M_ROI (map x ~f ~fv)
      | M1.M_Sum (a, b) ->
        map a ~f ~fv + map b ~f ~fv
      | M1.M_RSum (a, b) ->
	map a ~f ~fv +. map b ~f ~fv
      | M1.M_Prod (c, a) ->
        c * map a ~f ~fv
      | M1.M_RProd (c, a) ->
	c *. map a ~f ~fv
      | M1.M_Ite (q, a, b) ->
        M_Ite (Formula.map q ~polarity ~f,
               map a ~f ~fv,
               map b ~f ~fv)
      | M1.M_RIte (q, a, b) ->
	M_RIte (Formula.map q ~polarity ~f,
	       map a ~f ~fv,
	       map b ~f ~fv)
      | M1.M_Var i ->
        M_Var (Id.(fv.f_id) i)
      | M1.M_App (a, b) ->
        M_App (map a ~f ~fv, map b ~f ~fv)

  let rec map_non_atomic :
  type s . ('c1, s) M1.t ->
    f:('c1 M1.atom ->
       polarity:[ `Both | `Negative | `Positive ] ->
       'c2 M2.atom Formula.t) ->
    fv:(('c1, 'c2) Id.id_mapper) ->
    ('c2, s) t =
    let polarity = `Both in
    fun s ~f ~fv ->
      match s with
      | M1.M_Bool g ->
        M_Bool (Formula.map_non_atomic g ~polarity ~f)
      | M1.M_Int i ->
        M_Int i
      | M1.M_Real i -> M_Real i
      | M1.M_ROI x -> M_ROI (map_non_atomic x ~f ~fv)
      | M1.M_Sum (a, b) ->
        map_non_atomic a ~f ~fv + map_non_atomic b ~f ~fv
      | M1.M_RSum (a, b) -> map_non_atomic a ~f ~fv +. map_non_atomic b ~f ~fv
      | M1.M_Prod (c, a) ->
        c * map_non_atomic a ~f ~fv
      | M1.M_RProd (c, a) -> c *. map_non_atomic a ~f ~fv
      | M1.M_Ite (q, a, b) ->
        M_Ite (Formula.map_non_atomic q ~polarity ~f,
               map_non_atomic a ~f ~fv,
               map_non_atomic b ~f ~fv)
      | M1.M_RIte (q, a, b) -> M_RIte (Formula.map_non_atomic q ~polarity ~f,
				       map_non_atomic a ~f ~fv,
				       map_non_atomic b ~f ~fv)
      | M1.M_Var i ->
        M_Var (Id.(fv.f_id) i)
      | M1.M_App (a, b) ->
        M_App (map_non_atomic a ~f ~fv,
               map_non_atomic b ~f ~fv)

end

module Make_term_iter (M : Term_with_ops) = struct

  type ('i, 'a) t_arrow__ =
    {a_f : 't . ('i, 't) M.t -> 'a}

  type polarity = [`Positive | `Negative | `Both]

  let rec iter :
  type r s . ('c, r) M.t ->
    f  : ('c , unit) t_arrow__ ->
    fa : ('c M.atom -> polarity:polarity -> unit) ->
    unit =
    fun m ~f:({a_f} as f) ~fa ->
      a_f m;
      match m with
      | M.M_Bool g ->
        Formula.iter_atoms g ~f:fa ~polarity:`Both
      | M.M_Int _ ->
        ()
      | M.M_Real _ ->
      	()
      | M.M_Sum (m1, m2) ->
        iter m1 ~f ~fa;
        iter m2 ~f ~fa
      | M.M_Prod (_, m) ->
        iter m ~f ~fa
      | M.M_Ite (g, m1, m2) ->
        Formula.iter_atoms g ~f:fa ~polarity:`Both;
        iter m1 ~f ~fa;
        iter m2 ~f ~fa
      | M.M_Var _ ->
        ()
      | M.M_App (m1, m2) ->
        iter m1 ~f ~fa;
        iter m2 ~f ~fa

end

(* boxed terms *)

module Box = struct
  type 'i t = Box : ('i, _) M.t -> 'i t
end

module Ops = struct

  type 'a formula = 'a Formula.t (* Can remove this line if change Formula type on 
                                    Ops_intf.Prop inclusion (I did)*)

  (* The following sentence has 2 effects:
       - Checks if Ops_intf.Int is a subtype of M, that is, if all componens specified in 
         Ops_intf.Int are implemented in M, and meets the requirements of the signature.
       - Evaluates to the module M, hiding all components not specified in Ops_intf.Int*)
  include (M : Ops_intf.Int
           with type ('i, 'q) t := ('i, 'q) M.t
           and type int_plug := Int63.t)

  include (M : Ops_intf.Real
           with type ('i, 'q) t := ('i, 'q) M.t
           and type real_plug := Float.t)

  include A

  (*Same as sentence above, only includes the definition of Prop operators from Formula *)
  include (Formula : Ops_intf.Prop
           with type 'a t := 'a formula)

  (* As we already included definitions for Prop operators (from Formula) and Int and Float operators
    (from M), we only have to give a definition for Mixed operators*)

  let iite c a b = M.M_Ite (c, a, b)

  let (<) a b =
    Formula.F_Atom (A_Le (M.(a + M_Int Int63.one - b)))

  let (<=) a b =
    Formula.F_Atom (A_Le M.(a - b))

  let (=) a b =
    Formula.F_Atom (A_Eq M.(a - b))

  let (>=) a b = b <= a

  let (>) a b = b < a

  let rite c a b = M.M_RIte (c, a, b)

  let (<.) a b = Formula.F_Atom (A_LeR (M.(a +. (M_Real Float.(1.0)) -. b)))

  let (<=.) a b = Formula.F_Atom (A_LeR M.(a -. b))

  let (=.) a b = Formula.F_Atom (A_EqR M.(a -. b))

  let (>=.) a b = b <=. a

  let (>.) a b = b <. a
end
