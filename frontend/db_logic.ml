open Core.Std

open Db_logic_intf

module S : Schema = struct

  type _ t =
  | S_Int   :  int t
  | S_Bool  :  bool t
  | S_Real  :  float t
  | S_Pair  :  'a t * 'b t -> ('a * 'b) t

end

module rec M : (Logic_intf.Term_with_ops
                with type 'i atom = 'i A.t) =
  
  Logic.Make_term(A)

and R : (Row_with_ops with type ('i, 's) m := ('i, 's) M.t
                      and type 'i a := 'i A.t
                      and type 'u s := 'u S.t) =

struct

  open Terminology

  type ('i, _) t =
  | R_Int   :  ('i, int) M.t ->
    ('i, int) t
  | R_Bool  :  ('i, bool) M.t ->
    ('i, bool) t
  | R_Real  :  ('i, float) M.t ->
    ('i, float) t
  | R_Pair  :  ('i, 'r) t * ('i, 's) t ->
    ('i, 'r * 's) t

  let rec of_list :
  type s . s S.t ->
    (('i, int) M.t, 'i A.t Formula.t) ibeither list ->
    (('i, s) R.t *
        (('i, int) M.t, 'i A.t Formula.t) ibeither list) option =
    fun s l ->
      match s, l with
      | S.S_Int, H_Int x :: d ->
        Some (R_Int x, d)
      | S.S_Bool, H_Bool (Formula.F_Atom (A.A_Bool x)) :: d ->
        Some (R_Bool x, d)
      | S.S_Bool, H_Bool x :: d ->
        Some (R_Bool (M.M_Bool x), d)
      | S.S_Pair (s1, s2), l ->
        let open Option in
        of_list s1 l >>= (fun (x, l) ->
          of_list s2 l >>| (fun (y, l) ->
            R_Pair (x, y), l))
      | _ ->
        None

  let of_list s l =
    let open Option in
    of_list s l >>= function r, [] -> Some r | _ -> None


  let rec of_list' :
  type s . s S.t ->
    (('i, int) M.t, ('i, float) M.t, 'i A.t Formula.t) irbeither list ->
    (('i, s) R.t *
        (('i, int) M.t, ('i, float) M.t, 'i A.t Formula.t) irbeither list) option =
    fun s l ->
      match s, l with
      | S.S_Int, D_Int x :: d ->
        Some (R_Int x, d)
      | S.S_Real, D_Real x :: d ->
	Some (R_Real x, d)
      | S.S_Bool, D_Bool (Formula.F_Atom (A.A_Bool x)) :: d ->
        Some (R_Bool x, d)
      | S.S_Bool, D_Bool x :: d ->
        Some (R_Bool (M.M_Bool x), d)
      | S.S_Pair (s1, s2), l ->
        let open Option in
        of_list' s1 l >>= (fun (x, l) ->
          of_list' s2 l >>| (fun (y, l) ->
            R_Pair (x, y), l))
      | _ ->
        None

let of_list' s l =
    let open Option in
    of_list' s l >>= function r, [] -> Some r | _ -> None


  (* TODO : tail recursive *)
  let rec to_list :
  type s . ('i, s) t ->
    (('i, int) M.t, 'i A.t Formula.t) ibeither list =
    function
    | R_Int m ->
      [H_Int m]
    | R_Bool m ->
      [H_Bool (Formula.F_Atom (A.A_Bool m))]
    | R_Pair (m1, m2) ->
      List.append (to_list m1) (to_list m2)
    | R_Real _ -> raise (Failure "Case not considered in ibeither. This function will be replaced by to_list'")

  let rec to_list' :
  type s . ('i, s) t ->
    (('i, int) M.t, ('i, float) M.t, 'i A.t Formula.t) irbeither list =
    function
    | R_Int m ->
      [D_Int m]
    | R_Real m ->
      [D_Real m]
    | R_Bool m ->
      [D_Bool (Formula.F_Atom (A.A_Bool m))]
    | R_Pair (m1, m2) ->
      List.append (to_list' m1) (to_list' m2)



end

and D : (Db_with_ops
         with type 'i a := 'i A.t
         and type 's s := 's S.t
         and type ('i, 's) r := ('i, 's) R.t) =

struct

  type 'i a = 'i A.t
    
  type ('i, 's) r = ('i, 's) R.t

  type ('i, _) t =
  | D_Rel    :  'r S.t * (('i, 'r) R.t -> 'i a Formula.t) ->
    ('i, 'r) t
  | D_Input  :  'r S.t * ('i, 'r) r list ->
    ('i, 'r) t
  | D_Cross  :  ('i, 'r) t * ('i, 's) t ->
    ('i, 'r * 's) t
  | D_Sel    :  ('i, 'r) t * (('i, 'r) r -> 'i a Formula.t) ->
    ('i, 'r) t

  let sel a f = D_Sel (a, f)

  let cross a b = D_Cross (a, b)

  let rec schema_of_t :
  type r . ('i, r) t -> r S.t =
    function
    | D_Rel (s, _) ->
      s
    | D_Input (s, _) ->
      s
    | D_Cross (a, b) ->
      S.S_Pair (schema_of_t a, schema_of_t b)
    | D_Sel (a, _) ->
      schema_of_t a

end

and A :

  (Atom with type ('i, 's) d := ('i, 's) D.t
        and type ('i, 's) m := ('i, 's) M.t) = A

(* I copy-pasted the module below from lang_abstract.ml ; everything
   seems to work. There is no obvious way of functorizing Ops, because
   the atoms (A) differ. *)

module Ops = struct

  type 'a formula = 'a Formula.t

  include (M : Ops_intf.Int
           with type ('i, 'q) t := ('i, 'q) M.t
           and type int_plug := Int63.t)

  include A

  include (Formula : Ops_intf.Prop
           with type 'a t := 'a formula)

  let iite c a b = M.M_Ite (c, a, b)

  let (<) a b =
    Formula.F_Atom (A_Le (M.(a + M_Int Int63.one - b)))

  let (<=) a b =
    Formula.F_Atom (A_Le M.(a - b))

  let (=) a b =
    Formula.F_Atom (A_Eq M.(a - b))

  let (>=) a b = b <= a

  let (>) a b = b < a

  let sel = D.sel

  let cross = D.cross

  let exists l =
    Formula.F_Atom (A.A_Exists l)

  let toi x = M.M_Int (Int63.of_int x)

end
