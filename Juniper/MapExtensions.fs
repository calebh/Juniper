module MapExtensions

let merge map1 map2 = Map.fold (fun acc key value -> Map.add key value acc) map1 map2