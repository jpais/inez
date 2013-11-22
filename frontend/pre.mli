module Make : functor (I : Id.Accessors) -> sig

  type fun_id = I.c Id.Box_arrow.t

  type ibflat = (term, formula) Terminology.ifbeither

  and args = ibflat list

  and app = fun_id * args

  and sumt = Core.Std.Int63.t * term_base

  and sumtf = Core.Std.Float.t * term_base

  and sum = sumt list

  and sumf = sumtf list

  and iite = formula * term * term

  and term_base = private
                  | B_Var      of  (I.c, int) Id.t
		  | B_VarF     of  (I.c, float) Id.t
                  | B_Formula  of  formula
                  | B_App      of  app
                  | B_Ite      of  iite

  and term = private
             | G_Base  of  term_base
	     | G_Sum   of  sum Terminology.offset
             | G_SumF   of  sumf Terminology.float_offset

  and bite = formula * formula * formula

  and formula = private
                | U_Var   of  (I.c, bool) Id.t
                | U_Atom  of  term * Terminology.op'
                | U_Not   of  formula
                | U_And   of  formula list
                | U_App   of  app
                | U_Ite   of  bite

  with compare

  val hashable_sum : sum Core.Std.Hashtbl.Hashable.t
  val hashable_sumf : sumf Core.Std.Hashtbl.Hashable.t
  val hashable_args : args Core.Std.Hashtbl.Hashable.t
  val hashable_iite : iite Core.Std.Hashtbl.Hashable.t
  val hashable_bite : bite Core.Std.Hashtbl.Hashable.t
  val hashable_formula : formula Core.Std.Hashtbl.Hashable.t

  type ctx

  val make_ctx : unit -> ctx

  val dummy_formula : formula

  val flatten_int_term :
    ctx -> (I.c, int) Logic.M.t -> term

  val flatten_bool_term :
    ctx -> (I.c, bool) Logic.M.t -> formula

  val flatten_float_term:
    ctx -> (I.c, float) Logic.M.t -> term

  val flatten_formula :
    ctx -> I.c Logic.A.t Formula.t -> formula

  val flatten_term : ctx -> (I.c,'s) Logic.M.t -> ibflat

  val ff_ite : formula -> formula -> formula -> formula

end
