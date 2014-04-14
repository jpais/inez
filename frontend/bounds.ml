open Core.Std
open Terminology

module LL = struct
  let (<=) lb lb' =
    let lb =  Option.value lb  ~default:Int63.min_value
    and lb' = Option.value lb' ~default:Int63.min_value in
    Int63.(lb <= lb')
end

module UU = struct
  let (<=) ub ub' =
    let ub  = Option.value ub  ~default:Int63.max_value
    and ub' = Option.value ub' ~default:Int63.max_value in
    Int63.(ub <= ub')
end
  
module LU = struct
  let (<=) lb ub =
    let lb = Option.value lb ~default:Int63.min_value
    and ub = Option.value ub ~default:Int63.max_value in
    Int63.(lb <= ub)
end

module UL = struct
  let (<=) a b = LU.(b <= a)
end

module MLL = struct
  let (<=) lb lb' = 
    match lb, lb' with
      | SInt lb, SInt lb' -> 
	Int63.(lb <= lb')
      | SInt lb, NInt ->
	Int63.(lb <= min_value)
      | NInt, SInt lb ->
	Int63.(min_value <= lb)
      | SReal lb, SReal lb' ->
	Float.(lb <= lb')
      | SReal lb, NReal ->
	Float.(lb <= min_value)
      | NReal, SReal lb ->
	Float.(min_value <= lb) 
      | NInt, NInt ->
	true
      | NReal, NReal ->
	true
      | _, _ -> 
 	false
end

module MUU = struct
  let (<=) ub ub' = 
    match ub, ub' with
      | SInt ub, SInt ub' -> 
	Int63.(ub <= ub')
      | SInt ub, NInt ->
	Int63.(ub <= max_value)
      | NInt, SInt ub ->
	Int63.(max_value <= ub)
      | SReal ub, SReal ub' ->
	Float.(ub <= ub')
      | SReal ub, NReal ->
	Float.(ub <= max_value)
      | NReal, SReal ub ->
	Float.(max_value <= ub) 
      | NInt, NInt ->
	true
      | NReal, NReal ->
	true
      | _, _ ->
	false
end
  
module MLU = struct
  let (<=) lb ub =
    match lb, ub with 
      | SInt lb, SInt ub -> 
	Int63.(lb <= ub)
      | SInt lb, NInt ->
	Int63.(lb <= max_value)
      | NInt, SInt ub ->
	Int63.(min_value <= ub)
      | SReal lb, SReal ub ->
	Float.(lb <= ub)
      | SReal lb, NReal ->
	Float.(lb <= max_value)
      | NReal, SReal ub ->
	Float.(min_value <= ub) 
      | NInt, NInt ->
	true
      | NReal, NReal ->
	true
      | _, _ ->
	false
end

module MUL = struct
  let (<=) a b = MLU.(b <= a)
end

