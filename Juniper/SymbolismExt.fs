module SymbolismExt

open Extensions

// Extracts a solution from an And system of equations (ie, call this after IsolateVariable has been called)
let extractSolution (system : Symbolism.MathObject) (sym : Symbolism.Symbol) : Symbolism.MathObject option =
    match system with
    | :? Symbolism.And as and_ ->
        and_.args |>
        Seq.fold
            (fun ret elem ->
                match ret with
                | Some _ -> ret
                | None ->
                    match elem with
                    | :? Symbolism.Equation as eq ->
                        if eq.a.Equals(sym) then
                            Some (eq.b)
                        else
                            None
                    | _ ->
                        None)
            None
    | :? Symbolism.Equation as eq ->
        if eq.a.Equals(sym) then
            Some (eq.b)
        else
            None

let rec heuristicSimplify (m : Symbolism.MathObject) : Symbolism.MathObject =
    match m with
    | :? Symbolism.And as ad ->
        let args' =
            ad.args |>
            List.ofSeq |>
            List.map heuristicSimplify
        // Check to see if the list contains a false
        if args' |> List.contains (new Symbolism.Bool(false) :> Symbolism.MathObject) then
            (new Symbolism.Bool(false) :> Symbolism.MathObject)
        else
            match args' |> List.except [new Symbolism.Bool(true)] with
            | [] -> (new Symbolism.Bool(true) :> Symbolism.MathObject)
            | [arg] -> arg
            | reducedArgs -> (new Symbolism.And(reducedArgs |> Array.ofList) :> Symbolism.MathObject)
    | :? Symbolism.Or as o ->
        let args' =
            o.args |>
            List.ofSeq |>
            List.map heuristicSimplify
        if args' |> List.contains (new Symbolism.Bool(true) :> Symbolism.MathObject) then
            (new Symbolism.Bool(true) :> Symbolism.MathObject)
        else
            match args' |> List.except [new Symbolism.Bool(false)] with
            | [] -> (new Symbolism.Bool(false) :> Symbolism.MathObject)
            | [arg] -> arg
            | reducedArgs -> (new Symbolism.Or(reducedArgs |> Array.ofList) :> Symbolism.MathObject)
    | :? Symbolism.Equation as eq ->
        if (!> eq) then
            (new Symbolism.Bool(true) :> Symbolism.MathObject)
        else
            match eq.a with
            | :? Symbolism.Number as n1 ->
                match eq.b with
                | :? Symbolism.Number as n2 ->
                    if n1.Equals(n2) then
                        (new Symbolism.Bool(true) :> Symbolism.MathObject)
                    else
                        (new Symbolism.Bool(false) :> Symbolism.MathObject)
                | _ ->
                    m
            | _ ->
                m
    | _ ->
        m
