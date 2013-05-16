open Core.Std

(* module Id = (Int63 : Id_intf.Full) *)
module Id = Int63

module M = struct
  
  type ('c, 'u) t = Id.t * 'u Lang_types.t

  let sexp_of_t _ f x =
    Tuple.T2.sexp_of_t Id.sexp_of_t (Lang_types.sexp_of_t f) x

  let compare _ _ (id1, _) (id2, _) =
    Id.compare id1 id2

end

include M

module Box = struct

  type 'c t = Box : ('c, _) M.t -> 'c t

  let compare _ x y =
    Pervasives.compare x y

  let sexp_of_t f (Box x) =
    let g _ = Sexplib.Sexp.Atom "" in
    let x = sexp_of_t f g x in
    Sexplib.Sexp.(List [Atom "Box"; x])

end

module Box_arrow = struct

  type 'c t = Box : ('c, _ -> _) M.t -> 'c t

  let compare _ x y =
    Pervasives.compare x y

  let sexp_of_t f (Box x) =
    let g _ = Sexplib.Sexp.Atom "" in
    let x = sexp_of_t f g x in
    Sexplib.Sexp.(List [Atom "Box"; x])

end

(* explicit polymorphism; we need System F types in lang_concrete *)
type 'i t_arrow_type =
  { a_f : 't . ('i, 't) t -> 't Lang_types.t }

module type Generators = sig
  type c
  val gen_id : 'u Lang_types.t -> (c, 'u) t
end

module type Accessors = sig
  type c
  val type_of_t : (c, 'u) t -> 'u Lang_types.t
  val type_of_t' : c t_arrow_type
  val compare_c : c -> c -> int
  val sexp_of_c : c -> Sexplib.Sexp.t
end

module type S = sig
  include Generators
  include Accessors with type c := c
end

module Make (U : Unit.S) : S = struct

  (* [c] is empty and abstract outside this module. Applying the
     functor produces a different [c] each time. We tag IDs and
     expressions with [c], so that expressions with IDs that come from
     different contexts cannot be mixed. *)
  type c

  (* FIXME : clean up (i.e., do not raise exceptions) and put this in
     lang_types *)
  module TypeBox = struct
    module T = struct
      include Lang_types.Box
      let t_of_sexp _ = raise (Unreachable.Exn _here_)
      let hash = Hashtbl.hash
    end
    include T
    include Hashable.Make(T)
  end

  let m = TypeBox.Table.create () ~size:64

  let update_id = Option.map ~f:Id.succ

  let gen_id :
  type u . u Lang_types.t -> (c, u) t =
    fun x ->
      let x' = TypeBox.Box x in
      match Hashtbl.find m x' with
      | Some id ->
        Hashtbl.change m x' update_id; id, x
      | None ->
        let id = Id.succ Id.zero in
        Hashtbl.replace m x' id; Id.zero, x

  let type_of_t :
  type u . (c, u) t -> u Lang_types.t =
    Tuple.T2.get2

  let type_of_t' = { a_f = type_of_t }

  let compare_c _ _ = 0

  let sexp_of_c _ = Unit.sexp_of_t ()

end
