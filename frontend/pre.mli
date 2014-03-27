module Make : functor (I : Id.Accessors) -> sig

  type fun_id = I.c Id.Box_arrow.t

  type ibflat = (term, term, formula) Terminology.irbeither

  and args = ibflat list

  and app = fun_id * args

  and sumt = Core.Std.Int63.t * term_base

  and mixed_sumt =   S_Int of Core.Std.Int63.t * term_base
		    | S_Real of Core.Std.Float.t * term_base

  and sum = sumt list

  and mixed_sum = mixed_sumt list

  and iite = formula * term * term

  and term_base = private
                  | B_IVar     of  (I.c, int) Id.t
		  | B_RVar     of  (I.c, float) Id.t
                  | B_Formula  of  formula
                  | B_App      of  app
                  | B_Ite      of  iite

  and term = private
             | G_Base  of  term_base
	     | G_Sum   of  sum Terminology.offset
	     | G_SumM  of  mixed_sum Terminology.roffset
       
	    

  and bite = formula * formula * formula

  and formula = private
                | U_Var   of  (I.c, bool) Id.t
                | U_Atom  of  term * Terminology.op'
                | U_Not   of  formula
                | U_And   of  formula list
                | U_App   of  app
                | U_Ite   of  bite

  with compare

  val hashable_sum       : sum Core.Std.Hashtbl.Hashable.t
  val hashable_mixed_sum : mixed_sum Core.Std.Hashtbl.Hashable.t
  val hashable_args      : args Core.Std.Hashtbl.Hashable.t
  val hashable_iite      : iite Core.Std.Hashtbl.Hashable.t
  val hashable_bite      : bite Core.Std.Hashtbl.Hashable.t
  val hashable_formula   : formula Core.Std.Hashtbl.Hashable.t

  type ctx

  val make_ctx : unit -> ctx

  val dummy_formula : formula

  val flatten_int_term :
    ctx -> (I.c, int) Logic.M.t -> term

  val flatten_bool_term :
    ctx -> (I.c, bool) Logic.M.t -> formula

  val flatten_mixed_term:
    ctx -> (I.c, float) Logic.M.t -> term

  val flatten_formula :
    ctx -> I.c Logic.A.t Formula.t -> formula

  val flatten_term : ctx -> (I.c,'s) Logic.M.t -> ibflat

  val ff_ite : formula -> formula -> formula -> formula

end
