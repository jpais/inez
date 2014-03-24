module type S = sig

  type c
 
  type (_, _) term_plug
  type _ atom_plug  
   


  val constrain : c atom_plug Formula.t -> unit

  val minimize : (c, int) term_plug -> unit

  val minimize_real : (c, float) term_plug -> unit

  val solve : unit -> Terminology.result

  val fresh_int_var : unit -> (c, int) term_plug

  val fresh_bool_var : unit -> c atom_plug Formula.t

  val fresh_real_var : unit -> (c, float) term_plug

  val ideref : (c, int) term_plug -> Core.Std.Int63.t option

  val bderef : c atom_plug Formula.t -> bool option

  val rderef : (c, float) term_plug -> Core.Std.Float.t option

  val toi : int -> (c, int) term_plug

  val to_real :  (c, int) term_plug ->  (c, float) term_plug

  val gen_id : 's Type.t -> (c, 's) Id.t

  val string_of_result : Terminology.result -> string

  val solve_print_result : unit -> unit

  val argv : string array

end
