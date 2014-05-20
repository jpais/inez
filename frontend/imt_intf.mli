open Core.Std
open Terminology

module type S_ivar = sig

  (** integer variable *)
  type ivar

  val compare_ivar : ivar -> ivar -> int

  val hash_ivar : ivar -> int

  val sexp_of_ivar : ivar -> Sexplib.Sexp.t

end

module type S_bvar = sig
  
  (** boolean variable *)
  type bvar

  val compare_bvar : bvar -> bvar -> int

  val hash_bvar : bvar -> int

  val sexp_of_bvar : bvar -> Sexplib.Sexp.t

end

module type S_rvar = sig

  (** Real variable *)
  type rvar

  val compare_rvar : rvar -> rvar -> int

  val hash_rvar : rvar -> int

  val sexp_of_rvar : rvar -> Sexplib.Sexp.t

end

module type S_essentials = sig

  (** context *)
  type ctx

  include S_ivar

  include S_bvar

  include S_rvar

  val ivar_of_bvar : bvar -> ivar

  val bvar_of_ivar : ivar -> bvar

  val rvar_of_ivar : ivar -> rvar

end

module type S_uf = sig

  type f

  val compare_f : f -> f -> int

  val hash_f : f -> int

  val sexp_of_f : f -> Sexplib.Sexp.t

  (** dummy function symbol *)
  val dummy_f : f

end

module type S_access = sig

  include S_essentials

  include S_uf

  val new_f : ctx -> string -> int -> f

  (** define an integer variable with optional lower and upper
      bounds *)
  val new_ivar : ctx -> mip_type -> ivar

  val new_ivar' : ctx -> Core.Std.Int63.t option -> Core.Std.Int63.t option -> ivar

  (** define a boolean variable *)
  val new_bvar : ctx -> bvar

  (** define a real variable *)
  val new_rvar : ctx -> Core.Std.Float.t option -> Core.Std.Float.t option -> rvar

  (** [negate_bvar ctx v] = not v *)
  val negate_bvar : ctx -> bvar -> bvar

  (** [add_eq ctx i rhs] asserts i = rhs *) 
  val add_eq : ctx -> ivar isum -> Int63.t -> unit

  val add_real_eq : ctx -> (ivar, rvar) ireither rsum -> Float.t -> unit

  (** [add_le ctx i rhs] asserts i <= rhs *) 
  val add_le : ctx -> ivar isum -> Int63.t -> unit

  val add_real_le : ctx -> (ivar, rvar) lp_type -> Float.t -> unit

  (** [add_indicator ctx v i] asserts v => (i <= rhs) *) 
  val add_indicator :
    ctx -> bvar signed -> ivar isum -> Int63.t -> unit

  (** [add_real_indicator ctx v r] asserts v => (i <= rhs) *)
  val add_real_indicator :
    ctx -> bvar signed -> (ivar, rvar) lp_type -> Float.t -> unit

  (** [add_clause ctx l] asserts l (viewed as a clause) *)
  val add_clause : ctx -> bvar signed list -> unit

  (** [add_call v f l] enforces v = f(l) *)
  val add_call :
    ctx -> ivar option offset -> f -> ivar option offset list ->
    unit

  val add_objective : ctx -> ivar isum -> [ `Duplicate | `Ok ]

  val add_real_objective : ctx -> (ivar, rvar) lp_type -> [ `Duplicate | `Ok ]

  val solve : ctx -> result

  val ideref : ctx -> ivar -> Int63.t option

  val bderef : ctx -> bvar -> bool option

  val rderef : ctx -> rvar -> Float.t option

  val write_ctx : ctx -> string -> unit

end

module type S_int_bounds = sig

  type ctx

  type sol

  type t

  val get_lb_local : ctx -> t -> Int63.t option
    
  val get_ub_local : ctx -> t -> Int63.t option

  val set_lb_local :
    ctx -> t -> Int63.t -> [`Infeasible | `Ok | `Tightened]

  val set_ub_local :
    ctx -> t -> Int63.t -> [`Infeasible | `Ok | `Tightened]

  val ideref_sol : ctx -> sol -> t -> Int63.t

end

module type S_real_bounds = sig

  type ctx

  type sol

  type t

  val get_real_lb_local : ctx -> t -> Float.t option

  val get_real_ub_local : ctx -> t -> Float.t option

  val set_real_lb_local :
    ctx -> t -> Float.t -> [`Infeasible | `Ok | `Tightened]

  val set_real_ub_local :
    ctx -> t -> Float.t -> [`Infeasible | `Ok | `Tightened]

  val rderef_sol : ctx -> sol -> t -> Float.t

end


module type S_dp_access_bounds = sig

  type sol

  include S_essentials

  include S_int_bounds with type ctx := ctx 
		       and type t := ivar
		       and type sol := sol
  include S_real_bounds with type ctx := ctx
			and type t:= rvar
			and type sol := sol
		       
  val bderef_local : ctx -> bvar -> bool option

  val bderef_sol : ctx -> sol -> bvar -> bool

end


module type S_dp_access = sig

  include S_dp_access_bounds

  val ibranch :
    ctx -> ivar -> float -> [`Ok | `Fail]

  val ibranch_nary :
    ctx -> ivar ->
    middle:float -> n:int -> width:float ->
    [`Ok | `Fail]

  val rbranch :
    ctx -> rvar -> float -> [`Ok | `Fail]

  val rbranch_nary :
    ctx -> rvar ->
    middle:float -> n:int -> width:float ->
    [`Ok | `Fail]

   val bbranch :
    ctx -> bvar -> [`Ok | `Fail]

end


module type Dvars_access = sig

  type ctx_plug

  type sol_plug
  
  include (S_int_bounds
           with type ctx := ctx_plug
           and type sol := sol_plug)

  val sexp_of_t : t -> Sexplib.Sexp.t

  val compare : t -> t -> int

  val hashable : t Hashtbl.Hashable.t

end


module type Dvars_real_access = sig

  type ctx_plug

  type sol_plug

  include (S_real_bounds
           with type ctx := ctx_plug
           and type sol := sol_plug)

  val sexp_of_t : t -> Sexplib.Sexp.t

  val compare : t -> t -> int

  val hashable : t Hashtbl.Hashable.t

end


module type S_cut_gen_access = sig

  include S_dp_access_bounds

  module Dvars :
    (Dvars_access
     with type ctx_plug := ctx
     and type sol_plug := sol)

  module Drvars :
    (Dvars_real_access
       with type ctx_plug := ctx
       and type sol_plug := sol)

   val add_real_cut_local :
     ctx -> rvar Terminology.rexpr -> unit

   val add_cut_local :
     ctx -> ivar Terminology.iexpr -> unit

end


module type S_unit_creatable = sig
  include S_access
  include (Ctx_intf.S_creatable
           with type ctx := ctx
           and type carg := unit)
end

module type S_creatable = sig
  include S_access
  include (Ctx_intf.S_creatable with type ctx := ctx)
end

module type S_dp = sig

  type ivar_plug
  type bvar_plug
  type rvar_plug

  include Ctx_intf.S_unit_creatable

  module F

    (S : S_dp_access
     with type ivar := ivar_plug
     and type bvar := bvar_plug
     and type rvar := rvar_plug) :

  sig

    val push_level :
      ctx -> S.ctx -> unit

    val backtrack :
      ctx -> S.ctx -> unit

    val check :
      ctx -> S.ctx -> S.sol -> bool

    val propagate :
      ctx -> S.ctx -> response

    val branch :
      ctx -> S.ctx -> [`Ok | `Fail]

  end

end

module type S_with_dp = sig
    
  include S_essentials
  include S_uf

  module F

    (D : S_dp
     with type ivar_plug := ivar
     and type bvar_plug := bvar
     and type rvar_plug := rvar) :

  sig

    include
      (S_essentials
       with type ctx = ctx
       and type ivar = ivar
       and type bvar = bvar
       and type rvar = rvar)
      
    include
      (S_uf with type f = f)
      
    include
      (S_access
       with type ctx := ctx
       and type ivar := ivar
       and type bvar := bvar
       and type rvar := rvar
       and type f := f)

    val register_ivar :
      ctx -> ivar -> unit

    val register_bvar :
      ctx -> bvar -> unit

    val register_rvar :
      ctx -> rvar -> unit

    val make_ctx : D.ctx -> ctx

  end

end

module type S_cut_gen = sig

  type ivar_plug
  type bvar_plug
  type rvar_plug
  type dvar_int_plug
  type dvar_real_plug
 
  include Ctx_intf.S_unit_creatable

  module F

    (S : S_cut_gen_access
     with type ivar := ivar_plug
     and type bvar := bvar_plug
     and type rvar := rvar_plug
     and type Dvars.t = dvar_int_plug
     and type Drvars.t = dvar_real_plug):

  sig

    val push_level :
      ctx -> S.ctx -> unit

    val backtrack :
      ctx -> S.ctx -> unit

    val check :
      ctx -> S.ctx -> S.sol -> bool

    val generate :
      ctx -> S.ctx -> S.sol ->
      [ `Unknown | `Sat | `Unsat_Cut_Gen | `Cutoff ]

  end

end

module type S_with_cut_gen = sig
    
  include S_essentials
  include S_uf

  type sol

  module Dvars : sig

    include
      (Dvars_access
       with type ctx_plug := ctx
       and type sol_plug := sol)

    val create_dvar :
      ctx -> ivar option offset -> ivar option offset -> t

    val get_left : ctx -> t -> ivar option offset

    val get_right : ctx -> t -> ivar option offset

  end

  module Drvars : sig

    include 
      (Dvars_real_access
       with type ctx_plug := ctx
       and type sol_plug := sol)

    val create_drvar :
      ctx -> rvar option roffset -> rvar option roffset -> t

    val get_left : ctx -> t -> rvar option roffset

    val get_right : ctx -> t -> rvar option roffset

  end

  module F

    (D : S_cut_gen
     with type ivar_plug := ivar
     and type bvar_plug := bvar
     and type rvar_plug := rvar
     and type dvar_int_plug  := Dvars.t
     and type dvar_real_plug := Drvars.t) :

  sig

    include
      (S_essentials
       with type ctx = ctx
       and type ivar = ivar
       and type bvar = bvar
       and type rvar = rvar)
      
    include
      (S_uf with type f = f)
      
    include
      (S_access
       with type ctx := ctx
       and type ivar := ivar
       and type bvar := bvar
       and type rvar := rvar
       and type f := f)

    val make_ctx : D.ctx -> ctx

    val create_dvar :
      ctx ->
      ivar option offset ->
      ivar option offset ->
      Dvars.t

    val create_drvar :
      ctx ->
      rvar option roffset ->
      rvar option roffset ->
      Drvars.t
   
  end




end

