(* The following example was taken from 
Castillo, E., Conejo A.J., Pedregal, P., Garc ́ R. and Alguacil, N. (2002).
"Building and Solving Mathematical Programming Models in Engineering and
Science." 
Pure and Applied Mathematics Series, Wiley, New York.
*)

(* number of power units *)
let i = 3
(* number of time intervals on the planning horizon*)
let k = 3

(* startup costs per unit, constant for all time periods*)
let startup = [|20.0;18.0;5.0|]
(*shutdown cost per unit*)
let shutdown = [|0.5;0.3;1.0 |]
(* fixed cost per unit *)
let fixed = [|5.0;7.0;6.0|]
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


type unit = {u_id : int};;
type interval = {i_id : int};;

let units =  List.init i ~f:(fun u_id -> {u_id});;
let intervals = List.init k ~f:(fun i_id -> {i_id});;

let next_interval i = {i_id = i.i_id + 1};;
let prev_interval i = {i_id = i.i_id - 1};;

let make_ui_boolean_map ulist ilist =
  let ui_map =
    let size = List.length ulist * List.length ilist in
    Hashtbl.Poly.create ~size () in
  List.iter ulist ~f:(fun u ->
    List.iter ilist ~f:(fun i ->
      let x = fresh_int_var() in
      constrain(~logicr(x >= 0));
      constrain(~logicr(x <= 1));
      let key = u,i and data = x in
      Hashtbl.replace ui_map ~key ~data));
  fun u i -> Hashtbl.find_exn ui_map (u,i);;     

let make_ui_int_map ulist ilist =
  let ui_map =
    let size = List.length ulist * List.length ilist in
    Hashtbl.Poly.create ~size () in
  List.iter ulist ~f:(fun u ->
    List.iter ilist ~f:(fun i ->
      let x = fresh_int_var() in
      constrain(~logicr(x >= 0));
      let key = u,i and data = x in
      Hashtbl.replace ui_map ~key ~data));
  fun u i -> Hashtbl.find_exn ui_map (u,i);;     



(*list of binary variables representing if the unit i is started up at the begining of period k*)
let starting = make_ui_boolean_map units intervals;;

(*list of binary variables representing if the unit i is shut down at the begining of period k*)

let shutting = make_ui_boolean_map units intervals;;

(*list of variables representing if the unit i is online during period k*)

let online = make_ui_boolean_map units intervals;;

(*output power of unit i during period k*)

let output = make_ui_int_map units intervals;;


(* ============================================ Constrains =============================================*)

(*Any unit at any time  must operate above its minimum output power and below its maximum output power*)

constrain(
  ~logicr (forall units ~f:(
    fun u -> forall intervals ~f:(
      fun i -> (Int63.of_int (min_pow.(u.u_id))) * (online u i) <= (output u i)))));;

constrain(
  ~logicr(forall units ~f:(
    fun u -> forall intervals ~f:(
      fun i -> (Int63.of_int (max_pow.(u.u_id))) * (online u i) >= (output u i)))));;

(*From one time period to the next one, any power unit cannot increase its output power above 
a maximum power increment, called the rampup limit.*)

let rampup_constrain unit =
  List.iter intervals ~f:(fun i ->
    if (i.i_id) < ((List.length intervals) - 1) 
    then( (if i.i_id = 0 
          then constrain(~logicr((output unit i) - (toi (init_pow.(unit.u_id))) <=  
                                  (toi (max_rampup.(unit.u_id))))));
           constrain(~logicr((output unit (next_interval i)) - (output unit i) <= 
                             (toi (max_rampup.(unit.u_id)))))
    )
  );;

let rampdown_constrain unit = 
  List.iter intervals ~f:(fun i ->
    if (i.i_id) < ((List.length intervals) - 1) 
    then( if i.i_id = 0 
          then constrain(~logicr( (toi (init_pow.(unit.u_id))) - (output unit i) <=  
                                  (toi (max_rampdown.(unit.u_id)))));
               constrain(~logicr( (output unit i) - (output unit (next_interval i)) <= 
                                  (toi (max_rampdown.(unit.u_id)))))
        )
    else ()
  );;

List.iter units ~f:rampup_constrain;;
List.iter units ~f:rampdown_constrain;;


(*Any unit that is online can be shut down but not started up, and analogously,
any unit that is offline can be started up but not shut down*)

let status_constrain () =
  List.iter units ~f:(fun unit ->
  List.iter intervals ~f:(fun i ->
    if (i.i_id) = 0 
    then constrain( ~logicr((starting unit i) - (shutting unit i) = 
                  (online unit i) - (toi (init_online.(unit.u_id)))))
    else constrain(~logicr((starting unit i) - (shutting unit i) = 
                  (online unit i) - (online unit (prev_interval i))))
  ));;
status_constrain();;


(*The demand should be satisfied in every period: The sum of the output of each unit for each interval has to be equal to the demand*)

constrain(
  ~logicr(forall intervals ~f:(
    fun i -> sum units ~f:(
      fun u -> 
	(output u i)) = toi (demand.(i.i_id))
)));;


(* security constraints should be satisfied in all intervals: the total output power available should be larger than the actual demand by a specified amount *)

constrain(
~logicr(forall intervals ~f:(
  fun i -> sum units ~f:(
    fun u -> 
      (Int63.of_int (max_pow.(u.u_id))) * (online u i)) >= 
      (toi (demand.(i.i_id))) + (toi (reserve.(i.i_id))))));;


let z = ~logicr(sumr intervals ~f:(
                 fun i -> sumr units ~f:(
		   fun u -> fixed.(u.u_id)    *. roi(online u i) +.
                            variable.(u.u_id) *. roi(output u i) +. 
                            startup.(u.u_id)  *. roi(starting u i) +.    
                            shutdown.(u.u_id) *. roi(shutting u i))));;


(* Force an integer objective value 
let obj_var=
  let v = fresh_int_var() in
  constrain(~logicr(roi(v) =. z));v;;
*)
let obj_var = 
  let v = fresh_real_var() in
  constrain(~logicr(v =. z));v;;

minimize_real obj_var;;


let print_solution list =
  List.iter units ~f:(fun u ->
    List.iter intervals ~f:(fun i ->
      (match ideref (list u i) with
	| Some x -> printf "%s" (Int63.to_string x)
	| None -> raise (Failure "Error while reading the variable"));
      printf "   ");
    printf "\n"
);;

