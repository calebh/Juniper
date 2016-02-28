module ListExtensions

let hasDuplicates lst : bool =
    not (Set.count (Set.ofList lst) = List.length lst)