module Error
open FParsec
open System.IO

exception TypeError of string
exception SemanticError of string

// Get position of the error (starting line and column, end line and column) in the form of a string to be used
// for error messages.
let posString (p1 : Position, p2' : Position) : string =
    let p2 =
        if p1 = p2' then
            // The error should span at least one character
            new Position(p2'.StreamName, p2'.Index, p2'.Line, p2'.Column + 1L)
        else
            p2'
    let p1l = p1.Line - 1L
    let p2l = p2.Line - 1L
    let p1c = p1.Column - 1L
    let p2c = p2.Column - 1L
    let inRange line column =
        let notInRange = line < p1l ||
                         line > p2l ||
                         (line = p1l && column < p1c) ||
                         (line = p2l && column >= p2c)
        not notInRange
    let badCode =
        if File.Exists p1.StreamName then
            let lines = File.ReadAllLines p1.StreamName
            let relevantLines = lines.[int(p1l) .. int(p2l)]
            let arrows = Array.create relevantLines.Length (Array.create 0 ' ')
            for line in p1l .. p2l do
                let line' = line - p1l
                let lineLength = relevantLines.[int(line')].Length
                let arrowLine = Array.create lineLength ' '
                Array.set arrows (int(line')) arrowLine
                for column in 0 .. lineLength - 1 do
                    if inRange line (int64(column)) then
                        Array.set arrowLine column '^'
            let flattenedArrows = List.ofArray arrows |> List.map System.String.Concat
            let final = List.zip (List.ofArray relevantLines) flattenedArrows |> List.map (fun (a,b) -> a+"\n"+b+"\n") |> System.String.Concat
            sprintf "\n\n%s\n" final
        else
            ""
    sprintf "file %s, line %d column %d to line %d column %d%s" p1.StreamName (p1l + 1L) p1c (p2l + 1L) p2c badCode

let errStr pos err = lazy(sprintf "%s\n\n%s" (List.map posString pos |> String.concat "\n\n") err)