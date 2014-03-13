(* The following example was taken from 
Castillo, E., Conejo A.J., Pedregal, P., Garc ́ R. and Alguacil, N. (2002).
"Building and Solving Mathematical Programming Models in Engineering and
Science." 
Pure and Applied Mathematics Series, Wiley, New York.
*)

open Script;;
open Core.Std;;

(* Problem definition *)

let n = 7;;   (* Number of cities *)
let m = 6;;   (* Number of potential locations*)

assert(n >= 1 && m >= 1);;

(* 
opening_cost[i] is the fixed cost of building a factory at location i
 *)
let opening_cost = [|10;10;10;10;10;10|] ;;
assert(Array.length(opening_cost) = m);;

(* 
profit[i][j]  represents the profit of selling to the city i a unit of product fabricated at location j. 
*)
let profit = [|[| 4.0; 4.0;3.5;1.3;0.5;-1.0|];
	       [| 4.5; 4.5;5.0;3.0;1.0; 0.0|];
	       [| 2.5; 2.5;4.0;5.0;1.5; 1.5|];
	       [| 0.5; 4.2;3.5;3.3;5.0; 3.3|];
	       [| 1.0; 3.5;4.5;5.5;4.0; 4.0|];
	       [| 0.5; 1.5;1.5;1.8;5.5; 4.5|];
	       [|-3.5;-0.5;0.0;1.3;3.0; 2.0|]|] ;;
assert(Array.fold profit ~init:true ~f:(fun b l -> b && Array.length l = m) && (Array.length profit = n));; 
	  

(* capacity[i] is the capacity of the factory located at i*)
let capacity = [|6;6;6;6;6;6|];;
assert(Array.length(capacity) = m);;

(* demand[i] is the demand in units of product of city i*)
let demand = [|1.5;2.0;3.0;4.0;2.5;1.0;2.0|];;
assert(Array.length(demand) = n);;

type city = {c_id: int};;     (* Represents a city*)
type location = {l_id: int};; (* Represents a potential location for a factory*)


let cities    = List.init n ~f:(fun c_id -> {c_id});;
let locations = List.init m ~f:(fun l_id -> {l_id});;

let make_cl_map lcities lloc = 
  let cl_map =
    let size = List.length lcities * List.length lloc in
    Hashtbl.Poly.create ~size () in
  List.iter lcities ~f:(fun c ->
    List.iter lloc ~f:(fun l ->
      let x = fresh_real_var() in
      constrain (~logicr(x >=. 0.0));
      let key = c, l and data = x in
      Hashtbl.replace cl_map ~key ~data));
  fun c l -> Hashtbl.find_exn cl_map (c, l);;

let make_fl_map lloc =
  let fl_map =
    let size = List.length lloc in
    Hashtbl.Poly.create ~size () in
  List.iter lloc ~f:(fun l ->
    let y = fresh_int_var() in
    constrain (~logicr(y >= 0));
    constrain (~logicr(y <= 1));
    let key = l and data = y in
    Hashtbl.replace fl_map ~key ~data);
  fun l -> Hashtbl.find_exn fl_map l;;


(*
Expected production from each facility to each city 
*)
let production = make_cl_map cities locations ;;

(* 
Locations where a factory will be built
*)
let build = make_fl_map locations;;

(* CONSTRAINS *)

(* Satisfy each city demands *)
constrain
  (~logicr 
      (forall cities ~f:(fun c -> sumr locations ~f:(fun l -> (production c l)) =. Logic.M.M_Real(demand.(c.c_id)))));;
  
  
(* The production level of each factory cannot exceed its capacity*)
constrain
  (~logicr
    (forall locations
      ~f:(fun l -> sumr cities ~f:(fun c -> (production c l)) <=. roi(Int63.of_int(capacity.(l.l_id)) * (build l)))));;
  

(* Objective Function *)
maximize_real
(  ~logicr(
    (sumr cities ~f:(fun c -> 
           (sumr locations ~f:(fun l -> (profit.(c.c_id).(l.l_id) *. (production c l))))))
 -. (sumr locations  ~f:(fun l -> roi(((Int63.of_int(opening_cost.(l.l_id))) * (build l))))))
);;


(* Printing Solution *)

let should_build location =
  match List.nth locations (location-1) with
    | Some i -> ideref_print (sprintf("Build in L%d?:") location) (build i)
    | None -> raise (Failure "Out of bounds");;

let exp_prod city location =
  match List.nth cities (city-1), List.nth locations (location-1)  with
    | Some x, Some y -> rderef_print (sprintf("Production from Location %d to City %d") location city) (production x y)
    | _ -> raise (Failure "Out of bounds");;

let print_production () =
  List.iter locations ~f:(fun l ->
    if (ideref (build l) = (Some Int63.one))
    then( List.iter cities ~f:(fun c ->
          (match rderef (production c l) with
	     | Some x -> printf "%f" x
	     | None -> raise (Failure "Error while reading the variable"));
          printf "  ");
	  printf "\n")
);;
