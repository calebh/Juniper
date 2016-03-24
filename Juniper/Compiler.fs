module Compiler
open Ast

let mutable indentationLevel = 0
let mutable isNewLine = true
let indent () = indentationLevel <- indentationLevel + 1
let unindent () = indentationLevel <- indentationLevel - 1

let indentId () =
    indent()
    ""

let unindentId () =
    unindent()
    ""

let output (str : string) : string =
    if isNewLine then
        isNewLine <- false
        (String.replicate indentationLevel "    ") + str
    else
        str

let newline () =
    isNewLine <- true
    "\n"

let rec compileType (ty : TyExpr) : string =
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
        | TyModuleQualifier {module_ = (_, _, module_); name=(_, _, name)} ->
            output module_ +
            output "::" +
            output name
        | TyName (_, _, name) ->
            output name
        | TyApply {tyConstructor=(_, _, tyConstructor); args=(_, _, args)} ->
            compileType tyConstructor +
            output "<"

and compileLeftAssign (left : LeftAssign) : string =
    match left with
        | VarMutation {varName=(_, _, varName)} ->
            output varName
        | ArrayMutation {array=(_, _, array); index=index} ->
            output "(" +
            compileLeftAssign array +
            output ")[" +
            compile index +
            output "]"
        | RecordMutation {record=(_, _, record); fieldName=(_, _, fieldName)} ->
            output "(" +
            compileLeftAssign record +
            output ")." +
            output fieldName

and compile ((_, ty, expr) : PosAdorn<Expr>) : string =
    match expr with
        | IfElseExp {condition=condition; trueBranch=trueBranch; falseBranch=falseBranch} ->
            output "(" +
            compile condition +
            output " ? " +
            newline() +
            indentId() +
            compile trueBranch +
            unindentId() +
            newline() +
            output ":" +
            newline() +
            indentId() +
            compile falseBranch +
            output ")" +
            unindentId()
        | SequenceExp (_, Some tySeq, sequence) ->
            let len = List.length sequence
            output "(([&]() -> " +
            compileType tySeq +
            output " {" +
            newline() +
            indentId() +
            ((List.mapi (fun i seqElement ->
                (if i = len - 1 then
                    output "return "
                else
                    output "") +
                compile seqElement +
                output ";" +
                newline()
            ) sequence) |> String.concat "") +
            unindentId() +
            output "})())"
        | AssignExp {left=(_, _, left); right=right; ref=(_, _, ref)} ->
            output "(" +
            (if ref then
                output "*"
            else
                "") +
            compileLeftAssign left +
            output " = " +
            compile right +
            output ")"

and compileTemplate (template : Template) : string = 
    let tyVars = template.tyVars |> unwrap |> List.map (unwrap >> (+) "typename ")
    let capVars = template.capVars |> unwrap |> List.map (unwrap >> (+) "int ")
    output "template<" +
    (List.append tyVars capVars |> String.concat ", " |> output) +
    output ">"

and compileCap (cap : CapacityExpr) : string =
    ""

and compileTemplateApply (templateApp : TemplateApply) : string =
    output "<" +
    ((List.append
        (templateApp.tyExprs |> unwrap |> List.map (unwrap >> compileType))
        (templateApp.capExprs |> unwrap |> List.map (unwrap >> compileCap))) |> String.concat ", ") +
    output ">"

and compileDec (dec : Declaration) =
    match dec with
        | FunctionDec {name=(_, _, name); template=maybeTemplate; clause=(_, _, clause)} ->
            (match maybeTemplate with
                | Some (_, _, template) ->
                    compileTemplate template +
                    newline()
                | None ->
                    output "") +
            (clause.returnTy |> unwrap |> compileType) +
            output " " +
            output name +
            output "(" +
            ((clause.arguments |> unwrap |> List.map (fun (ty, name) ->
                                                         (ty |> unwrap |> compileType) +
                                                         output " " +
                                                         (name |> unwrap |> output))) |> String.concat ", ") +
            output ") {" +
            newline() +
            indentId() +
            compile clause.body +
            unindentId() +
            newline() +
            output "}"
        | RecordDec {name=(_, _, name); fields=fields; template=maybeTemplate} ->
            (match maybeTemplate with
                | Some (_, _, template) ->
                    compileTemplate template +
                    newline()
                | None ->
                    output "") +
            output "struct " +
            output name +
            output " {" +
            newline() +
            indentId() +
            ((fields |> unwrap |> List.map (fun (fieldTy, fieldName) ->
                                                compileType fieldTy +
                                                output " " +
                                                output fieldName +
                                                output ";")) |> (String.concat "")) +
            newline() +
            unindentId() +
            output "};"
        | LetDec {varName=(_, _, varName); typ=(_, _, typ); right=right} ->
            compileType typ +
            output " " +
            output varName +
            output " = " +
            compile right