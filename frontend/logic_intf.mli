module type Term = sig

  type 'i atom
    
  type ('i, _) t =
  | M_Bool  :  'i atom Formula.t ->
    ('i, bool) t
  | M_Int   :  Core.Std.Int63.t ->
    ('i, int) t
  | M_Real :  Core.Std.Float.t -> 
    ('i, float) t
  | M_ROI   : ('i, int) t -> ('i, float) t
  | M_Sum   :  ('i, int) t * ('i, int) t ->
    ('i, int) t
  | M_FSum  :  ('i, float) t * ('i,float) t ->
    ('i, float) t
  | M_Prod  :  Core.Std.Int63.t * ('i, int) t ->
    ('i, int) t
  | M_FProd :  float * ('i, float) t -> 
    ('i, float) t
  | M_Ite   :  'i atom Formula.t * ('i, int) t * ('i, int) t ->
    ('i, int) t
  | M_FIte  :  'i atom Formula.t * ('i, float) t * ('i, float) t ->
    ('i, float) t
  | M_Var   :  ('i, 's) Id.t ->
    ('i, 's) t
  | M_App   :  ('i, 'r -> 's) t * ('i, 'r) t ->
    ('i, 's) t

end

module type Term_with_ops = sig

  include Term

  val zero : ('a, int) t
  val one : ('a, int) t
  val zeror : ('a, float) t
 
  val roi : ('a, int) t -> ('a, float) t
  
  (* conversions *)

  val of_int63 : Core.Std.Int63.t -> ('a, int) t

  (* type utilities *)

  val type_of_t :
    ('i, 's) t -> f:'i Id.t_arrow_type -> 's Type.t
  
  (* traversal *)

  val fold :
    ('i, 's) t ->
    init:'a ->
    f:('a -> 'i atom Formula.t -> 'a) -> 'a

  (* INT infix operators *)

  include (Ops_intf.Int with type ('i, 's) t := ('i, 's) t
                        and type int_plug := Core.Std.Int63.t)

  (* FLOAT infix operators *)
  include (Ops_intf.Float with type ('i, 's) t := ('i, 's) t
                          and type float_plug := Core.Std.Float.t)	    
end

module type Atom = sig

  type (_, _) term_plug

   
  (*Added constructors for A_Le and A_Eq Float*)

  type 'i t =
  | A_Bool  of  ('i, bool)  term_plug
  | A_Le    of  ('i, int)   term_plug
  | A_LeF   of  ('i, float) term_plug
  | A_Eq    of  ('i, int)   term_plug
  | A_EqF   of  ('i, float) term_plug

end
