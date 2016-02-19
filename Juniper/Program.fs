// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.

module Progam
open Microsoft.FSharp.Text.Lexing

[<EntryPoint>]
let main argv =
    let parseFromFile (fileName:string) = 
        let fileStr = System.IO.File.ReadAllText fileName
        let lexbuf = LexBuffer<char>.FromString fileStr
        try
            Parser.start Lexer.token lexbuf
        with
          | _ -> printfn "Syntax error on line %d, column %d" (lexbuf.StartPos.Line+1) lexbuf.StartPos.Column
                 failwith "Parser error"
    
    
    let asts = List.map parseFromFile (List.ofArray argv)
    let typedAsts = TypeChecker.typecheck asts
    //let ast = parseFromFile @"C:\Users\caleb\Documents\juniper_programs\test.jun"
    printfn "%A" typedAsts
    System.Console.ReadKey() |> ignore
    0 // return an integer exit code
