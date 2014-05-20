open Core.Std

type 't unop            =  't -> 't

type 't binop           =  't -> 't -> 't

type 't ternop          =  't -> 't -> 't -> 't

type op                 =  O_Lt | O_Le | O_Eq | O_Ge | O_Gt
with compare, sexp

type op'                =  O'_Le | O'_Eq | O'_MLe | O'_MEq
with compare, sexp

type 'v monomial        =  Core.Std.Int63.t * 'v
with compare, sexp

type 'v rmonomial       =  Core.Std.Float.t * 'v
with compare, sexp

type 'v offset          =  'v * Core.Std.Int63.t
with compare, sexp

type 'v roffset         =  'v * Core.Std.Float.t
with compare, sexp

type 'v isum            =  'v monomial list
with compare, sexp

type 'v rsum            =  'v rmonomial list
with compare, sexp

type ('i, 'r) ireither = W_Int of 'i | W_Real of 'r
with compare, sexp

type ('i, 'r) iroption =       SInt of 'i 
			     | SReal of 'r
			     | NInt
			     | NReal
 with compare, sexp_of


(** Represents the type of linear program. J_Int is a pure integer program and J_Mix a mixed program*)
type ('i,'r) lp_type      =   LP_Int of 'i isum
			    | LP_Mix of ('i,'r) ireither rsum
with compare, sexp

type 'v iexpr           =  'v isum offset
with compare, sexp

type 'v rexpr            =  'v rsum roffset
with compare, sexp

type mip_type           =    T_Int  of (Core.Std.Int63.t option *  Core.Std.Int63.t option)
                           | T_Real of (Core.Std.Float.t option *  Core.Std.Float.t option)
with compare, sexp

type result             =  R_Opt | R_Unbounded | R_Sat
                           | R_Unsat | R_Unknown
with compare, sexp

type response           =  N_Ok | N_Unsat | N_Tightened
with compare, sexp

type 't signed          =  S_Pos of 't | S_Neg of 't
with compare, sexp

type ('i, 'b) ibeither  =  H_Int of 'i | H_Bool of 'b
with compare, sexp

type ('i, 'r, 'b) irbeither = D_Int of 'i | D_Real of 'r | D_Bool of 'b
with compare, sexp

type 'a diff            =  'a * 'a
with compare, sexp
