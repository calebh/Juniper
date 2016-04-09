﻿// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.

module Progam
open Microsoft.FSharp.Text.Lexing


[<EntryPoint>]
let main argv =
    let stdLibrary = ["Prelude"; "Signal"; "Io"; "Maybe"; "List"; "Time"; "Math"; "Button"]
    let executingDir = System.IO.Path.GetDirectoryName(System.Reflection.Assembly.GetExecutingAssembly().Location);
    let stdFiles = stdLibrary |> List.map (fun name -> executingDir + "/junstd/" + name + ".jun")
    let parseFromFile (fileName:string) = 
        let fileStr = System.IO.File.ReadAllText fileName
        let lexbuf = LexBuffer<char>.FromString fileStr
        lexbuf.EndPos <- { pos_bol = 0;
                           pos_fname=fileName;
                           pos_cnum=0;
                           pos_lnum=0 }
        try
            Parser.start Lexer.token lexbuf
        with
          | _ -> printfn "Syntax error in %s on line %d, column %d" fileName (lexbuf.StartPos.Line + 1) (lexbuf.StartPos.Column + 1);
                 failwith "Syntax error"
    let fnames = List.append stdFiles (List.map System.IO.Path.GetFullPath (List.ofArray argv))
    let asts = List.map parseFromFile fnames
    try
        let typedAsts = TypeChecker.typecheckProgram asts fnames
        let compiledProgram = Compiler.compileProgram typedAsts
        printfn "%s" compiledProgram
        0
    with
        Failure(msg) ->
            1