module Make

  (S : sig
    include Imt_intf.S_rvar
    include Imt_intf.S_real_bounds with type t := rvar
    val name_real_diff : ctx -> rvar -> rvar -> Core.Std.Float.t -> rvar option
  end) :

sig

  include (Imt_intf.S_real_bounds
           with type ctx := S.ctx
           and type sol := S.sol)

  val sexp_of_t : t -> Sexplib.Sexp.t

  val compare : t -> t -> int

  val hashable : t Core.Std.Hashtbl.Hashable.t

  val create_drvar :
    S.ctx ->
    S.rvar option Terminology.roffset ->
    S.rvar option Terminology.roffset ->
    t

  val get_left : S.ctx -> t -> S.rvar option Terminology.roffset
  
  val get_right : S.ctx -> t -> S.rvar option Terminology.roffset


end

