module NestedPair

type NestedPair<'a> = NestedPair of (NestedPair<'a> * NestedPair<'a>)
                    | NestedElem of 'a
                    | NestedEmpty
    
let ne elem =
    NestedElem elem

let rec nest lst =
    match lst with
    | head::tail -> NestedPair (head, nest tail)
    | [] -> NestedEmpty

type IOList = NestedPair<string>

let concat a b =
    NestedPair (a, b)

let rec map f pair =
    match pair with
    | NestedPair (left, right) -> NestedPair ((map f left), (map f right))
    | NestedElem elem -> NestedElem (f elem)
    | NestedEmpty -> NestedEmpty

let rec fold f accum pair =
    match pair with
    | NestedPair (left, right) ->
        let accum' = fold f accum left
        fold f accum' right
    | NestedElem elem ->
        f accum elem
    | NestedEmpty ->
        accum

let rec foldBack f accum pair =
    match pair with
    | NestedPair (left, right) ->
        let accum' = foldBack f accum right
        foldBack f accum' left
    | NestedElem elem ->
        f elem accum
    | NestedEmpty ->
        accum

let ioListToString (lst : IOList) =
    let builder = new System.Text.StringBuilder()
    let rec ioListToString' (lst : IOList) : unit =
        match lst with
        | NestedPair (left, right) ->
            builder.Append(ioListToString' left) |> ignore
            builder.Append(ioListToString' right) |> ignore
        | NestedElem elem ->
            builder.Append(elem) |> ignore
        | NestedEmpty ->
            ()
    ioListToString' lst |> ignore
    builder.ToString()