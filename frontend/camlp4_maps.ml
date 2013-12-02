open Camlp4.PreCast

exception Reserved of string

type y = Y_Int | Y_Bool | Y_Real

let gensym =
  let cnt = ref 0 in
  fun ?(prefix = "_x") () ->
    incr cnt;
    Printf.sprintf "%s__%03i_" prefix !cnt

let uf_ast_fun _loc mid mid' (l, rtype) =
  let fold l init =
    let f y acc =
      match y with
      | Y_Int ->
        <:expr< Type.Y_Int_Arrow $acc$ >>
      | Y_Bool ->
        <:expr< Type.Y_Bool_Arrow $acc$ >>
      | Y_Real -> 
        <:expr< Type.Y_Real_Arrow $acc$ >> in
    ListLabels.fold_right l ~f ~init
  and init =
    match rtype with
    | Y_Int ->  <:expr< Type.Y_Int >>
    | Y_Bool -> <:expr< Type.Y_Bool >>
    | Y_Real -> <:expr< Type.Y_Real >>
  and ret e = <:expr< $uid:mid$.M.M_Var ($uid:mid'$.gen_id $e$) >> in
  ret (fold l init)

let uf_ast_apps _loc mid init =
  ListLabels.fold_left2 ~init
    ~f:(fun acc id t ->
      let t =
        match t with
        | Y_Int ->
          <:expr< $id:id$ >>
	| Y_Real ->
	  <:expr< $id:id$ >>
        | Y_Bool ->
          <:expr< $uid:mid$.M.M_Bool $id:id$ >> in
      <:expr< $uid:mid$.M.M_App ($acc$, $t$) >>)

let ml_lambda_abstract _loc init =
  let f id acc = <:expr< fun $id:id$ -> $acc$ >> in
  ListLabels.fold_right ~init ~f

let uf_maybe_convert _loc mid y e =
  match y with
  | Y_Bool ->
    <:expr< Formula.F_Atom ($uid:mid$.A.A_Bool ($e$)) >>
  | Y_Int ->
    e
  | Y_Real ->
    e

let uf_ast _loc mid mid' (l, y) =
  let l_ids =
    let f _ = Ast.IdLid (_loc, gensym ()) in
    List.map f l
  and id = gensym ~prefix:"__uf_" () in
  let inside =
    ml_lambda_abstract _loc
      (uf_maybe_convert _loc mid y
         (uf_ast_apps _loc mid <:expr< $lid:id$ >> l_ids l))
      l_ids
  and binding = uf_ast_fun _loc  mid mid' (l, y) in
  <:expr< let $lid:id$ = $binding$ in $inside$ >> ;;

let rec type_of_uf ?acc:(acc = []) =
  function
  | <:expr< fun $lid:_$ -> $e$ >>
  | <:expr< fun _ -> $e$ >>
  | <:expr< fun ($lid:_$ : Int) -> $e$ >>
  | <:expr< fun (_ : Int) -> $e$ >> ->
    type_of_uf ~acc:(Y_Int :: acc) e
  | <:expr< fun (_ : Float) -> $e$ >> ->
    type_of_uf ~acc:(Y_Real :: acc) e
  | <:expr< fun ($lid:_$ : Bool) -> $e$ >>
  | <:expr< fun (_ : Bool) -> $e$ >> ->
    type_of_uf ~acc:(Y_Bool :: acc) e
  | <:expr< ~free >>
  | <:expr< (~free : Int) >> ->
    Some (List.rev acc, Y_Int)
  | <:expr< (~free : Float) >> ->
    Some (List.rev acc, Y_Real)
  | <:expr< (~free : Bool) >> ->
    Some (List.rev acc, Y_Bool)
  | _ ->
    None

let map_uf mid mid' = object

  inherit Ast.map as super
  
  method expr = function
  | <:expr@loc< fun $lid:_$ -> $_$ >>
  | <:expr@loc< fun ($lid:_$ : Int) -> $_$ >>
  | <:expr@loc< fun ($lid:_$ : Float) -> $_$ >>
  | <:expr@loc< fun ($lid:_$ : Bool) -> $_$ >>
  | <:expr@loc< fun _ -> $_$ >>
  | <:expr@loc< fun (_ : Int) -> $_$ >>
  | <:expr@loc< fun (_ : Float) -> $_$ >>
  | <:expr@loc< fun (_ : Bool) -> $_$ >> as e ->
    (match type_of_uf e with
    | Some y ->
      uf_ast loc mid mid' y
    | None ->
      e)
  | e ->
    super#expr e

end

let transform_logic_aux mid e =
  let _loc = Ast.loc_of_expr e in
  match e with
  | <:expr< true >> ->
    <:expr< Formula.F_True >>
  | <:expr< false >> ->
    <:expr< Formula.(F_Not F_True) >>
  | <:expr< $uid:mid$.M.M_Int $x$ * $uid:mid'$.M.M_Int $y$ >>
      when mid = mid' ->
    <:expr< $uid:mid$.M.M_Int (Int63.( * ) $x$ $y$) >>
  | <:expr<
      $uid:mid$.M.M_Int (Core.Std.Int63.of_string $str:s$) * $x$ >> ->
    <:expr<
      $uid:mid$.M.M_Prod (Core.Std.Int63.of_string $str:s$, $x$) >>
  | <:expr< $uid:mid$.M.M_Int $i1$ * $uid:mid'$.M.M_Int $i2$ >>
      when mid = mid' ->
    <:expr< $uid:mid$.M.M_Int (Core.Std.Int63.(i1 * i2)) >>
  | <:expr< $int:s$ >> ->
    <:expr< $uid:mid$.M.M_Int (Core.Std.Int63.of_string $str:s$) >>
  | <:expr< $int64:s$ >> ->
    <:expr< $uid:mid$.M.M_Int (Core.Std.Int63.of_string $str:s$) >>
  | _ ->
    e

let transform_real_logic_aux mid e =
  let _loc = Ast.loc_of_expr e in
  match e with
  | <:expr< true >> ->
    <:expr< Formula.F_True >>
  | <:expr< false >> ->
    <:expr< Formula.(F_Not F_True) >>
  | <:expr< $uid:mid$.M.M_Int $x$ * $uid:mid'$.M.M_Int $y$ >>
      when mid = mid' ->
    <:expr< $uid:mid$.M.M_Int (Int63.( * ) $x$ $y$) >>
  | <:expr< $uid:mid$.M.M_Float $x$ *. $uid:mid'$.M.M_Float $y$ >>
      when mid = mid' ->
    <:expr< $uid:mid$.M.M_Float (Float.( * ) $x$ $y$) >>
  | <:expr< $uid:mid$.M.M_Int (Core.Std.Int63.of_string $str:s$) * $x$ >> ->
    <:expr<
      $uid:mid$.M.M_Prod (Core.Std.Int63.of_string $str:s$, $x$) >>
  | <:expr< $uid:mid$.M.M_Float (Core.Std.Float.of_string $str:s$) *. $x$ >> ->
    <:expr<
      $uid:mid$.M.M_FProd (Core.Std.Float.of_string $str:s$, $x$) >>
  | <:expr< $uid:mid$.M.M_Int $i1$ * $uid:mid'$.M.M_Int $i2$ >>
      when mid = mid' ->
    <:expr< $uid:mid$.M.M_Int (Core.Std.Int63.(i1 * i2)) >>
  | <:expr< $int:s$ >> ->
    <:expr< $uid:mid$.M.M_Float (Core.Std.Float.of_string $str:s$) >> 
  | <:expr< $flo:s$ >> ->
    <:expr< $uid:mid$.M.M_Float (Core.Std.Float.of_string $str:s$) >>
  | <:expr< $int64:s$ >> ->
    <:expr< $uid:mid$.M.M_Float (Core.Std.Float.of_string $str:s$) >> 
  | _ ->
    e

let map_logic_aux mid =
  Ast.map_expr (transform_logic_aux mid)

let map_real_logic_aux mid =
  Ast.map_expr (transform_real_logic_aux mid)

let transform_logic mid = function
  | <:expr@loc< ~logic $e$ >> ->
    <:expr@loc< let open $uid:mid$.Ops in
                $(map_logic_aux mid)#expr e$ >>
  | <:expr@loc< ~logicr $e$ >> ->
    <:expr@loc< let open $uid:mid$.Ops in
                $(map_real_logic_aux mid)#expr e$ >>
  | e ->
    e

let map_logic mid =
  Ast.map_expr (transform_logic mid)
