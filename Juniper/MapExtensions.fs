module MapExtensions

// Merges two maps together
// map2 overrides the entries in map1 in the case
// of a duplicate key
let merge map1 map2 = Map.fold (fun acc key value -> Map.add key value acc) map1 map2