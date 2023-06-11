module Extensions

let flip f a b = f b a

let inline (!>) (x:^a) : ^b = ((^a or ^b) : (static member op_Implicit : ^a -> ^b) x)

// Merges two maps together
// map2 overrides the entries in map1 in the case
// of a duplicate key
module Map =
    let merge map1 map2 = Map.fold (fun acc key value -> Map.add key value acc) map1 map2

    let mergeMany maps = List.fold merge Map.empty maps

    let singleton k v = Map.add k v Map.empty

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

    let rec findFixpoint k m =
        match Map.tryFind k m with
        | Some k' ->
            findFixpoint k' m
        | None ->
            k

    let mapAlt f m = Map.fold (fun acc key value ->
                                let (key', value') = f key value
                                Map.add key' value' acc) Map.empty m

    let invert m = mapAlt (fun key value -> (value, key)) m

    let keys m = m |> Map.toSeq |> Seq.map fst |> Set.ofSeq

    let values m = m |> Map.toSeq |> Seq.map snd

    let fromKeys f k = k |> List.ofSeq |> List.map (fun k -> (k, f k)) |> Map.ofList

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
    
    let ofListDuplicateKeys lst =
        lst |>
        List.fold (fun accum (key, value) -> match Map.tryFind key accum with
                                             | Some preExistingValues -> Map.add key (value::preExistingValues) accum
                                             | None -> Map.add key [value] accum) Map.empty

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

    let rec unzip5 lst =
        match lst with
        | [] ->
            ([], [], [], [], [])
        | (v, w, x, y, z)::rest ->
            let (vs, ws, xs, ys, zs) = unzip5 rest
            (v::vs, w::ws, x::xs, y::ys, z::zs)
    
    let rec mapFilter f lst =
        match lst with
        | [] -> []
        | x::xs ->
            match f x with
            | Some v -> v::(mapFilter f xs)
            | None-> mapFilter f xs

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

    let mapFold (f : 'state -> 'a -> ('b * 'state)) (accum : 'state) (o : option<'a>) : (option<'b> * 'state) =
        match o with
        | None ->
            (None, accum)
        | Some x ->
            let (x', accum') = f accum x
            (Some x', accum')

module Choice =
    let splitChoice2 (lst : Choice<'a, 'b> list) =
        List.foldBack
            (fun elem (lstA, lstB) ->
                match elem with
                | Choice1Of2 a ->
                    (a::lstA, lstB)
                | Choice2Of2 b ->
                    (lstA, b::lstB))
            lst
            ([], [])

    let getChoice1Of2 (Choice1Of2 x) = x