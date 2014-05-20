open Terminology
open Core.Std

type 'i quantified = ('i, int) Id.t

module X = struct

  type 'c t =
    'c quantified list *
      ((('c, int) Logic.M.t * ('c, int) Logic.M.t * op') list *
          (('c, int) Logic.M.t * ('c, int) Logic.M.t * op'))

end

include X

module Ops = struct

  include (Logic.M : Ops_intf.Int
           with type ('i, 'q) t := ('i, 'q) Logic.M.t
           and type int_plug := Int63.t)

  let (<=) a b = a, b, Terminology.O'_Le

  let (<) a b = a, b - Logic.M.one, Terminology.O'_Le

  let (>=) a b = b, a, Terminology.O'_Le

  let (>) a b = b < a

  let (=) a b = a, b, Terminology.O'_Eq

end

module Flat = struct

  (* no operators here; normalizing to <= *)

  type 'i hypothesis = ('i, int) Flat.t iexpr * ('i, int) Flat.t iexpr

  type 'i cut = ('i, int) Flat.t iexpr

  type 'i t = 'i quantified list * 'i hypothesis list * 'i cut

  let iter_subterms (_, h, (l, _) : 'i t) ~f =
    let f (_, x) = f x in
    List.iter l ~f;
    let f ((l1, _), (l2, _)) = List.iter l1 ~f; List.iter l2 ~f in
    List.iter h ~f

end
