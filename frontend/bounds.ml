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
      | W_Int (Some lb), W_Int (Some lb') -> 
	Int63.(lb <= lb')
      | W_Int (Some lb), W_Int None ->
	Int63.(lb <= min_value)
      | W_Int None, W_Int (Some lb) ->
	Int63.(min_value <= lb)
      | W_Real (Some lb), W_Real (Some lb') ->
	Float.(lb <= lb')
      | W_Real (Some lb), W_Real None ->
	Float.(lb <= min_value)
      | W_Real None, W_Real (Some lb) ->
	Float.(min_value <= lb) 
      | W_Real None, W_Real None ->
	true
      | W_Int None, W_Int None ->
	true
      | _, _ -> 
 	false
end

module MUU = struct
  let (<=) ub ub' = 
    match ub, ub' with
      | W_Int (Some ub), W_Int (Some ub') -> 
	Int63.(ub <= ub')
      | W_Int (Some ub), W_Int None ->
	Int63.(ub <= max_value)
      | W_Int None, W_Int (Some ub) ->
	Int63.(max_value <= ub)
      | W_Real (Some ub), W_Real (Some ub') ->
	Float.(ub <= ub')
      | W_Real (Some ub), W_Real None->
	Float.(ub <= max_value)
      | W_Real None, W_Real (Some ub) ->
	Float.(max_value <= ub) 
      | W_Int None, W_Int None->
	true
      | W_Real None, W_Real None ->
	true
      | _, _ ->
	false
end
  
module MLU = struct
  let (<=) lb ub =
    match lb, ub with 
      | W_Int (Some lb), W_Int (Some ub) -> 
	Int63.(lb <= ub)
      | W_Int (Some lb), W_Int None->
	Int63.(lb <= max_value)
      | W_Int None, W_Int (Some ub) ->
	Int63.(min_value <= ub)
      | W_Real (Some lb), W_Real (Some ub) ->
	Float.(lb <= ub)
      | W_Real (Some lb), W_Real None->
	Float.(lb <= max_value)
      | W_Real None, W_Real (Some ub) ->
	Float.(min_value <= ub) 
      | W_Int None, W_Int None ->
	true
      | W_Real None, W_Real None->
	true
      | _, _ ->
	false
end

module MUL = struct
  let (<=) a b = MLU.(b <= a)
end

