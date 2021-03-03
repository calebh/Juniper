module Extensions

let flip f a b = f b a

// Merges two maps together
// map2 overrides the entries in map1 in the case
// of a duplicate key
module Map =
    let merge map1 map2 = Map.fold (fun acc key value -> Map.add key value acc) map1 map2

    // Map find, defaulting to the identity function if the key could
    // not be found in the map
    let findId k m =
        match Map.tryFind k m with
        | Some x -> x
        | None -> k

    let findDefault k deflt m =
        match Map.tryFind k m with
        | Some x -> x
        | None -> deflt

    let mapAlt f m = Map.fold (fun acc key value ->
                                let (key', value') = f key value
                                Map.add key' value' acc) Map.empty m

    let invert m = mapAlt (fun key value -> (value, key)) m

    let keys m = m |> Map.toSeq |> Seq.map fst |> Set.ofSeq

    let ofDict dictionary = 
        (dictionary :> seq<_>)
        |> Seq.map (|KeyValue|)
        |> Map.ofSeq

    let invertNonInjective m =
        Map.fold
            (fun acc k v ->
                let keys' =
                    match Map.tryFind v acc with
                    | Some keys ->
                        k::keys
                    | None ->
                        [k]
                Map.add v keys' acc)
            Map.empty
            m

module List =
    let hasDuplicates lst : bool = not (Set.count (Set.ofList lst) = List.length lst)

    let cons2 a b = a::b

    let foldlEq f init l1 l2 = List.fold (fun accum (e1, e2) -> f accum e1 e2) init (List.zip l1 l2)

    let rec unzip4 lst =
        match lst with
        | [] ->
            ([], [], [], [])
        | (w, x, y, z)::rest ->
            let (ws, xs, ys, zs) = unzip4 rest
            (w::ws, x::xs, y::ys, z::zs)

module Seq =
    let duplicates (xs: _ seq) =
      seq { let d = System.Collections.Generic.Dictionary(HashIdentity.Structural)
            let e = xs.GetEnumerator()
            while e.MoveNext() do
              let x = e.Current
              let mutable seen = false
              if d.TryGetValue(x, &seen) then
                if not seen then
                  d.[x] <- true
                  yield x
              else
                d.[x] <- false }

module String =
    /// Converts a string into a list of characters.
    let explode (s:string) =
        [for c in s -> c]

    /// Converts a list of characters into a string.
    let implode (xs:char list) =
        let sb = System.Text.StringBuilder(xs.Length)
        xs |> List.iter (sb.Append >> ignore)
        sb.ToString()

module Option =
    let flattenList (o : option<list<'a>>) =
        match o with
        | None -> []
        | Some xs -> xs