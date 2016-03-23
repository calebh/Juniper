module Extensions

// Merges two maps together
// map2 overrides the entries in map1 in the case
// of a duplicate key
module Map =
    let merge map1 map2 = Map.fold (fun acc key value -> Map.add key value acc) map1 map2

module List =
    let hasDuplicates lst : bool = not (Set.count (Set.ofList lst) = List.length lst)

