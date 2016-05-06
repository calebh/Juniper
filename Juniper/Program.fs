module Progam
open Microsoft.FSharp.Text.Lexing

exception SyntaxError of string

let parseArgs (args : string []) =
    let mutable flagName = None
    let mutable flagValues = []
    let mutable map = Map.empty
    for a in args do
        if a.StartsWith("-") then
            match flagName with
                | None -> ()
                | Some name ->
                    map <- Map.add name flagValues map
            flagName <- Some a
            flagValues <- []
        else
            flagValues <- List.append flagValues [a]
    match flagName with
        | None -> ()
        | Some name ->
            map <- Map.add name flagValues map
    map

let getArg possibleFlags argMap =
    Map.tryPick (fun flagName values -> if List.contains flagName possibleFlags then Some values else None) argMap

let isWindows =
    System.Environment.OSVersion.Platform = System.PlatformID.Win32NT

let helpText =
    let runTimeName = if isWindows then "Juniper.exe" else "juniper"
    ["usage: " + runTimeName + " -s s1.jun s2.jun ... sn.jun -o main.cpp";
     "  options:";
     "    -s, --source: The .jun Juniper source files to compile";
     "    -o, --output: The file in which the compiled C++ is written";
     "    -h, --help: View this help message"] |> String.concat "\n"

[<EntryPoint>]
let main argv =
    let argMap = parseArgs argv
    let maybeSourceFiles = getArg ["-s"; "--source"] argMap
    let maybeOutputFile = getArg ["-o"; "--output"] argMap
    let maybeHelp = getArg ["-h"; "--help"] argMap
    match (maybeSourceFiles, maybeOutputFile, maybeHelp) with
        | ((_, _, Some _) | (None, _, _) | (_, None, _)) | (_, Some [], _) ->
            printfn "%s" helpText
            0
        | (Some sourceFiles, Some (outputFile::_), _) ->
            // List of includes of custom Juniper std library modules
            let stdLibrary = ["Prelude"; "List"; "Signal"; "Io"; "Maybe"; "Time"; "Math"; "Button"; "Vector"]
            let executingDir = System.IO.Path.GetDirectoryName(System.Reflection.Assembly.GetExecutingAssembly().Location);
            // Make the include modules names by prepending the executing directory and /junstd/, and appending the .jun file extension
            let stdFiles = stdLibrary |> List.map (fun name -> "junstd/" + name + ".jun")
            // Lexer and parser operations on the file
            let parseFromFile (fileName:string) =
                let fileName' = (if System.IO.File.Exists(fileName) then
                                    fileName
                                 else
                                    executingDir + "/" + fileName) |> System.IO.Path.GetFullPath
                let fileStr = System.IO.File.ReadAllText fileName'
                let lexbuf = LexBuffer<char>.FromString fileStr
                lexbuf.EndPos <- { pos_bol = 0;
                                   pos_fname=fileName';
                                   pos_cnum=0;
                                   pos_lnum=0 }
                try
                    Parser.start Lexer.token lexbuf
                with
                  | _ -> raise <| SyntaxError (sprintf "Syntax error in %s" (TypeChecker.posString (lexbuf.StartPos, lexbuf.StartPos)))
            // All of the file names includes all the specified ones, plus the std Juniper library
            let fnames = List.append stdFiles sourceFiles
            try
                // Run parseFromFile (the lexer and parser)
                let asts = List.map parseFromFile fnames
                // Typecheck the ASTs
                let typedAsts = TypeChecker.typecheckProgram asts fnames
                // Compile to C++ the typechecked (and typed) ASTs
                let compiledProgram = Compiler.compileProgram typedAsts
                System.IO.File.WriteAllText (outputFile, compiledProgram)
                0
            with
                | (TypeChecker.TypeError err | TypeChecker.SemanticError err | SyntaxError err) ->
                    printfn "%s" err
                    1
                | :? System.IO.FileNotFoundException as ex ->
                    printf "%s" ex.Message
                    1