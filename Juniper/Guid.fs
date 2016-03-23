module Guid

let mutable uniqueCounter = 0

let int () =
    let res = uniqueCounter
    uniqueCounter <- uniqueCounter + 1
    res

let string () =
    sprintf "guid%d" (int ())