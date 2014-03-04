
(* number of power units *)
let i = 3
(* number of time intervals *)
let k = 3

(* startup costs per unit*)
let startup = [|20;18;5|]
(*shutdown cost per unit*)
let shutdown = [|0.5;0.3;1.0 |]
(* fixed cost per unit *)
let fixed = [|5;7;6|]
(* variable cost per unit *) 
let variable = [|0.100;0.125;0.150|]
(* minimum output power per unit*)
let min_pow = [|50;80;40|]
(* maximum output power per unit*)
let max_pow = [|350;200;140|]
(* maximum rampup power increment per unit *)
let max_rampup = [|200;100;100|]
(* maximum rampdown power decrement per unit *)
let max_rampdown = [|300;150;100|]
(* initial power output per unit before the first period*)
let init_pow = [|0;0;0|]
(* unit is online before the first period of planning? *)
let init_online = [|0;0;0|]
(* Demand per time interval *)
let demand = [|150;500;400|]
(* Required reserve over the demand per time interval*)
let reserve = [|15;50;40|]


let units =  List.init i ~f:(fun u_id -> {u_id});;
let intervals = List.init k ~f:(fun i_id -> {i_id});;


let make_ui_map ulist ilist =
  let ui_map =
    let size = List.length ulist * List.length ilist in
    Hashtbl.Poly.create ~size () in
  List.iter ulist ~f:(fun u ->
    List.iter ilist ~f(fun i ->
      let x = fresh_int_var() in
      constrain(~logicr(x >= 0));
      constrain(~logicr(x <= 1));
      let key = u,i and data = x in
      Hashtbl.replace ui_map ~key ~data));
  fun u i -> Hashtbl.find_exn ui_map (c,l);;     


(*list of binary variables representing if the unit i is started up at the begining of period k*)
let starting = make_ui_map units intervals;;

(*list of binary variables representing if the unit i is shut down at the begining of period k*)

let shutting = make_ui_map units intervals;;

(*list of variables representing if the unit i is online during period k*)

let online = make_ui_map units intervals;;

(*output power of unit i during period k*)

let output = make_ui_map units intervals;;


(* ============================================ Constrains =============================================*)

(*Any unit at any time  must operate above its minimum output power and below its maximum output power*)

min_pow(i) * online(i,t) <= output(i,t)
max_pow(i) * online(i,t) >= output(i,t)
