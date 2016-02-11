// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.

module Progam
open Microsoft.FSharp.Text.Lexing

[<EntryPoint>]
let main argv =
    let parseFromFile (fileName:string) = 
        let fileStr = System.IO.File.ReadAllText fileName
        let lexbuf = LexBuffer<char>.FromString fileStr
        Parser.start Lexer.token lexbuf
    
    let ast = parseFromFile @"C:\Users\caleb\Documents\juniper_programs\signal.jun"
    printfn "%A" ast
    System.Console.ReadKey() |> ignore
    0 // return an integer exit code
