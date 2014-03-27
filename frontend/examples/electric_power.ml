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
let startup = [|20000;18000;5000|]
(*shutdown cost per unit*)
let shutdown = [|500;300;1000 |]
(* fixed cost per unit *)
let fixed = [|5000;7000;6000|]
(* variable cost per unit *) 
let variable = [|100;125;150|]
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

let z = ~logicr(sum intervals ~f:(
                 fun i -> sum units ~f:(
		   fun u -> ( (Int63.of_int (fixed.(u.u_id   ))) * (online u i) +
                              (Int63.of_int (variable.(u.u_id))) * (output u i) + 
                              (Int63.of_int (startup.(u.u_id ))) * (starting u i) +    
                              (Int63.of_int (shutdown.(u.u_id))) * (shutting u i) ))));;



(* Force an integer objective value 
let obj_var=
  let v = fresh_int_var() in
  constrain(~logicr(v = z));v;;
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


let nth l n =
  match List.nth l (n-1) with
    | Some x -> x
    | None -> raise (Failure "Out of bounds")

let nth' l u i =
  l (nth units u) (nth intervals i)

let starting' u i = nth' starting u i;;
let shutting' u i = nth' shutting u i;;
let online' u i = nth' online u i;;
let output' u i = nth' output u i;;


(* Hand-made conditions*)

let online11 = fresh_int_var();;
let online12 = fresh_int_var();;
let online13 = fresh_int_var();;
let online21 = fresh_int_var();;
let online22 = fresh_int_var();;
let online23 = fresh_int_var();;
let online31 = fresh_int_var();;
let online32 = fresh_int_var();;
let online33 = fresh_int_var();;
constrain(~logicr(online11 >= 0));;
constrain(~logicr(online12 >= 0));;
constrain(~logicr(online13 >= 0));;
constrain(~logicr(online21 >= 0));;
constrain(~logicr(online22 >= 0));;
constrain(~logicr(online23 >= 0));;
constrain(~logicr(online31 >= 0));;
constrain(~logicr(online32 >= 0));;
constrain(~logicr(online33 >= 0));;
constrain(~logicr(online11 <= 1));;
constrain(~logicr(online12 <= 1));;
constrain(~logicr(online13 <= 1));;
constrain(~logicr(online21 <= 1));;
constrain(~logicr(online22 <= 1));;
constrain(~logicr(online23 <= 1));;
constrain(~logicr(online31 <= 1));;
constrain(~logicr(online32 <= 1));;
constrain(~logicr(online33 <= 1));;

let starting11 = fresh_int_var();;
let starting12 = fresh_int_var();;
let starting13 = fresh_int_var();;
let starting21 = fresh_int_var();;
let starting22 = fresh_int_var();;
let starting23 = fresh_int_var();;
let starting31 = fresh_int_var();;
let starting32 = fresh_int_var();;
let starting33 = fresh_int_var();;
constrain(~logicr(starting11 >= 0));;
constrain(~logicr(starting12 >= 0));;
constrain(~logicr(starting13 >= 0));;
constrain(~logicr(starting21 >= 0));;
constrain(~logicr(starting22 >= 0));;
constrain(~logicr(starting23 >= 0));;
constrain(~logicr(starting31 >= 0));;
constrain(~logicr(starting32 >= 0));;
constrain(~logicr(starting33 >= 0));;
constrain(~logicr(starting11 <= 1));;
constrain(~logicr(starting12 <= 1));;
constrain(~logicr(starting13 <= 1));;
constrain(~logicr(starting21 <= 1));;
constrain(~logicr(starting22 <= 1));;
constrain(~logicr(starting23 <= 1));;
constrain(~logicr(starting31 <= 1));;
constrain(~logicr(starting32 <= 1));;
constrain(~logicr(starting33 <= 1));;

let shutting11 = fresh_int_var();;
let shutting12 = fresh_int_var();;
let shutting13 = fresh_int_var();;
let shutting21 = fresh_int_var();;
let shutting22 = fresh_int_var();;
let shutting23 = fresh_int_var();;
let shutting31 = fresh_int_var();;
let shutting32 = fresh_int_var();;
let shutting33 = fresh_int_var();;
constrain(~logicr(shutting11 >= 0));;
constrain(~logicr(shutting12 >= 0));;
constrain(~logicr(shutting13 >= 0));;
constrain(~logicr(shutting21 >= 0));;
constrain(~logicr(shutting22 >= 0));;
constrain(~logicr(shutting23 >= 0));;
constrain(~logicr(shutting31 >= 0));;
constrain(~logicr(shutting32 >= 0));;
constrain(~logicr(shutting33 >= 0));;
constrain(~logicr(shutting11 <= 1));;
constrain(~logicr(shutting12 <= 1));;
constrain(~logicr(shutting13 <= 1));;
constrain(~logicr(shutting21 <= 1));;
constrain(~logicr(shutting22 <= 1));;
constrain(~logicr(shutting23 <= 1));;
constrain(~logicr(shutting31 <= 1));;
constrain(~logicr(shutting32 <= 1));;
constrain(~logicr(shutting33 <= 1));;

let output11 = fresh_int_var();;
let output12 = fresh_int_var();;
let output13 = fresh_int_var();;
let output21 = fresh_int_var();;
let output22 = fresh_int_var();;
let output23 = fresh_int_var();;
let output31 = fresh_int_var();;
let output32 = fresh_int_var();;
let output33 = fresh_int_var();;
constrain(~logicr(output11 >= 0));;
constrain(~logicr(output12 >= 0));;
constrain(~logicr(output13 >= 0));;
constrain(~logicr(output21 >= 0));;
constrain(~logicr(output22 >= 0));;
constrain(~logicr(output23 >= 0));;
constrain(~logicr(output31 >= 0));;
constrain(~logicr(output32 >= 0));;
constrain(~logicr(output33 >= 0));;

constrain(~logicr(50 * online11 <= output11));;
constrain(~logicr(50 * online12 <= output12));;
constrain(~logicr(50 * online13 <= output13));;
constrain(~logicr(80 * online21 <= output21));;
constrain(~logicr(80 * online22 <= output22));;
constrain(~logicr(80 * online23 <= output23));;
constrain(~logicr(40 * online31 <= output31));;
constrain(~logicr(40 * online32 <= output32));;
constrain(~logicr(40 * online33 <= output33));;

constrain(~logicr(output11 <= 350 * online11));;
constrain(~logicr(output12 <= 350 * online12));;
constrain(~logicr(output13 <= 350 * online13));;
constrain(~logicr(output21 <= 200 * online21));;
constrain(~logicr(output22 <= 200 * online22));;
constrain(~logicr(output23 <= 200 * online23));;
constrain(~logicr(output31 <= 140 * online31));;
constrain(~logicr(output32 <= 140 * online32));;
constrain(~logicr(output33 <= 140 * online33));;

let output10 = 0;;
let output20 = 0;;
let output30 = 0;;
let online10 = 0;;
let online20 = 0;;
let online30 = 0;;

constrain(~logicr(output11 - toi(output10) <= 200));;
constrain(~logicr(output12 - output11 <= 200));;
constrain(~logicr(output13 - output12 <= 200));;
constrain(~logicr(output21 - toi(output20) <= 100));;
constrain(~logicr(output22 - output21 <= 100));;
constrain(~logicr(output23 - output22 <= 100));;
constrain(~logicr(output31 - toi(output30) <= 100));;
constrain(~logicr(output32 - output31 <= 100));;
constrain(~logicr(output33 - output32 <= 100));;

constrain(~logicr(toi(output10) - output11 <= 300));;
constrain(~logicr(output11 - output12 <= 300));;
constrain(~logicr(output12 - output13 <= 300));;
constrain(~logicr(toi(output20) - output21 <= 150));;
constrain(~logicr(output21 - output22 <= 150));;
constrain(~logicr(output22 - output23 <= 150));;
constrain(~logicr(toi(output30) - output31 <= 100));;
constrain(~logicr(output31 - output32 <= 100));;
constrain(~logicr(output32 - output33 <= 100));;

constrain(~logicr(starting11 - shutting11 = online11 - toi(online10)));;
constrain(~logicr(starting12 - shutting12 = online12 - online11));;
constrain(~logicr(starting13 - shutting13 = online13 - online12));;
constrain(~logicr(starting21 - shutting21 = online21 - toi(online20)));;
constrain(~logicr(starting22 - shutting22 = online22 - online21));;
constrain(~logicr(starting23 - shutting23 = online23 - online22));;
constrain(~logicr(starting31 - shutting31 = online31 - toi(online30)));;
constrain(~logicr(starting32 - shutting32 = online32 - online31));;
constrain(~logicr(starting33 - shutting33 = online33 - online32));;

constrain(~logicr(output11 + output21 + output31 = 150));;
constrain(~logicr(output12 + output22 + output32 = 500));;
constrain(~logicr(output13 + output23 + output33 = 400));;

constrain(~logicr(350 * online11 + 200 * online21 + 140 * online31 >= 150 + 15));;
constrain(~logicr(350 * online12 + 200 * online22 + 140 * online32 >= 500 + 50));;
constrain(~logicr(350 * online13 + 200 * online23 + 140 * online33 >= 400 + 40));;

minimize(~logicr(
5000 * online11 + 5000 * online12 + 5000 * online13 + 
7000 * online21 + 7000 * online22 + 7000 * online23 + 
6000 * online31 + 6000 * online32 + 6000 * online33 +
100  * output11 + 100  * output12 + 100  * output13 + 
125  * output21 + 125  * output22 + 125  * output23 +
150  * output31 + 150  * output32 + 150  * output33 +
20000 * starting11 + 20000 * starting12 + 20000 * starting13 +
18000 * starting21 + 18000 * starting22 + 18000 * starting23 +
5000  * starting31 + 5000  * starting32 + 5000  * starting33 +
500  * shutting11 + 500  * shutting12 + 500  * shutting13 +
300  * shutting21 + 300  * shutting22 + 300  * shutting23 +
1000 * shutting31 + 1000 * shutting32 + 1000 * shutting33));;

ideref_print "output11" output11;;
ideref_print "output12" output12;;
ideref_print "output13" output13;;
ideref_print "output21" output21;;
ideref_print "output22" output22;;
ideref_print "output23" output23;;
ideref_print "output31" output31;;
ideref_print "output32" output32;;
ideref_print "output33" output33;;
