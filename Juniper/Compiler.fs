module Compiler
open Ast

let compiledResult = new System.Text.StringBuilder()

let mutable indentationLevel = 0
let mutable isNewLine = true
let indent () = indentationLevel <- indentationLevel + 1
let unindent () = indentationLevel <- indentationLevel - 1

let output (str : string) =
    if isNewLine then
        isNewLine <- false
        for i in 0 .. indentationLevel - 1 do
            compiledResult.Append("    ") |> ignore
    else
        ()
    compiledResult.Append(str) |> ignore

let newline () =
    isNewLine <- true
    compiledResult.Append("\n") |> ignore

let rec compileType (ty : TyExpr) =
    match ty with
        | BaseTy (_, _, bty) ->
            match bty with
                | TyUint8 -> output "uint8_t"
                | TyUint16 -> output "uint16_t"
                | TyUint32 -> output "uint32_t"
                | TyUint64 -> output "uint64_t"
                | TyInt8 -> output "int8_t"
                | TyInt16 -> output "int16_t"
                | TyInt32 -> output "int32_t"
                | TyInt64 -> output "int64_t"
                | TyFloat -> output "float"
                | TyBool -> output "bool"
                | TyUnit -> output "unit"

and compileLeftAssign (left : LeftAssign) : unit =
    match left with
        | VarMutation {varName=(_, _, varName)} ->
            output varName
        | ArrayMutation {array=(_, _, array); index=index} ->
            output "("
            compileLeftAssign array
            output ")["
            compile index
            output "]"
        | RecordMutation {record=(_, _, record); fieldName=(_, _, fieldName)} ->
            output "("
            compileLeftAssign record
            output ")."
            output fieldName

and compile ((_, ty, expr) : PosAdorn<Expr>) : unit =
    match expr with
        | IfElseExp {condition=condition; trueBranch=trueBranch; falseBranch=falseBranch} ->
            output "("
            compile condition
            output " ? "
            newline()
            indent()
            compile trueBranch
            unindent()
            newline()
            output ":"
            newline()
            indent()
            compile falseBranch
            output ")"
            unindent()
        | SequenceExp (_, Some tySeq, sequence) ->
            output "(([&]() -> "
            compileType tySeq
            output " {"
            newline()
            indent()
            let len = List.length sequence
            sequence |> List.iteri
                (fun i seqElement ->
                    if i = len - 1 then
                        ()
                    else
                        compile seqElement
                        output ";"
                        newline())
            output "return "
            compile (List.last sequence)
            output ";"
            newline()
            unindent()
            output "})())"
        | AssignExp {left=(_, _, left); right=right; ref=(_, _, ref)} ->
            output "("
            if ref then
                output "*"
            compileLeftAssign left
            output " = "
            compile right
            output ")"

and compileDec (dec : Declaration) =
    