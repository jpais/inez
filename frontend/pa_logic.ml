open Camlp4.PreCast
open Camlp4_maps

let _ =
  let m = (map_uf "Logic" "Script")#str_item in
  AstFilters.register_str_item_filter m;
  AstFilters.register_topphrase_filter m

let _ =
  let m = (map_logic "Logic")#str_item in
  AstFilters.register_str_item_filter m;
  AstFilters.register_topphrase_filter m
