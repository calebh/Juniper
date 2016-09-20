module Program2
open FParsec
open TypedAst
open Parse2
open Constraint

let program = "if true then () else 2 end"

[<EntryPoint>]
let main argv =
    try
        match run Parse2.expr program with
        //match run applyTemplateToFunc "List:foreach<int32>" with
        | Success(result, _, _) ->
            let (typedAst, constraints) = TypeChecker2.typeof (Ast2.unwrap result) ()
            printf "%A" (Constraint.solve constraints)
            printf "%A" typedAst
        | Failure(errorMsg, _, _) -> printfn "Failure: %s" errorMsg
    with
    | TypeError err -> printfn "%s" err
    System.Console.ReadKey() |> ignore
    0