module Make (Imt : Imt_intf.S_essentials) : sig

  include (Imt_intf.S_dp
           with type ivar_plug := Imt.ivar
           and type bvar_plug := Imt.bvar
	   and type rvar_plug := Imt.rvar)

  val print_stats : ctx -> unit

  val assert_membership :
    ctx ->
    Imt.bvar Core.Std.Hashtbl.key ->
    Imt.ivar option Terminology.offset list ->
    Imt.ivar option Terminology.offset list Core.Std.List.t ->
    fd:(Imt.ivar -> Imt.ivar -> Imt.ivar) ->
    frv:(Imt.ivar -> unit) -> unit

  val assert_mixed_membership : 
    ctx ->
    Imt.bvar Core.Std.Hashtbl.key ->
    (Imt.ivar option Terminology.offset, Imt.rvar option Terminology.roffset) Terminology.ireither list ->
    (Imt.ivar option Terminology.offset, Imt.rvar option Terminology.roffset) Terminology.ireither list Core.Std.List.t ->
    fd:((Imt.ivar, Imt.rvar) Terminology.ireither -> (Imt.ivar, Imt.rvar) Terminology.ireither -> (Imt.ivar, Imt.rvar) Terminology.ireither) ->
    frv:((Imt.ivar, Imt.rvar) Terminology.ireither -> unit) -> unit
end
