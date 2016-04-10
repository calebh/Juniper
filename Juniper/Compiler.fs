module Compiler
open Ast

// The following are used for automatically adding new lines line indentation to transpiled C++
let mutable indentationLevel = 0
let mutable isNewLine = true
let indent () = indentationLevel <- indentationLevel + 1
let unindent () = indentationLevel <- indentationLevel - 1
let mutable entryPoint = None

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

// In Juniper, death is a templated function that calls exit(1)
// They are templated so they can be wrapped in a type so they can have return values consistent in typing
// with whatever statement or function they may be a part of (for example, a function that returns an int will
// return death typed as an int, which will still exit the program).
let rec getDeathExpr (ty : TyExpr) : PosAdorn<Expr> =
    let deathFun = dummyWrap (ModQualifierExp {module_=dummyWrap "juniper"; name=dummyWrap "death"})
    let appliedDeath = TemplateApplyExp { func = deathFun;
                                          templateArgs = dummyWrap {tyExprs = dummyWrap [dummyWrap ty];
                                                                    capExprs = dummyWrap []}} |> dummyWrap
    wrapWithType
        ty
        (CallExp {func = appliedDeath;
                  args = dummyWrap []})

// Converts type from Juniper representation to C++ representation.
and compileType (ty : TyExpr) : string =
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
                | TyUnit -> output "Prelude::unit"
                | TyDouble -> output "double"
                | TyPointer -> output "juniper::shared_ptr<void>"
        | TyModuleQualifier {module_ = (_, _, module_); name=(_, _, name)} ->
            output module_ +
            output "::" +
            output name
        | TyName (_, _, name) ->
            output name
        | TyApply {tyConstructor=(_, _, tyConstructor); args=(_, _, args)} ->
            compileType tyConstructor + compileTemplateApply args
        | ForallTy (_, _, name) ->
            output name
        | ArrayTy {valueType=(_, _, valueType); capacity=(_, _, capacity)} ->
            output "juniper::array<" + compileType valueType + output "," + compileCap capacity + output ">"
        | FunTy { args=args; returnType=(_, _, returnType) } ->
            output "juniper::function<" + compileType returnType + output "(" +
            (args |> List.map (unwrap >> compileType) |> String.concat ",")
            + output ")>"
        | RefTy (_, _, ty) ->
            output "juniper::shared_ptr<" + compileType ty + ">"
        | TupleTy tys ->
            output (sprintf "Prelude::tuple%d<" (List.length tys)) +
            (tys |> List.map (unwrap >> compileType) |> String.concat ",") +
            output ">"

// Converts left side of a variable assignment to the C++ representation.
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
        | ModQualifierMutation {modQualifier=(_, _, {module_=(_, _, module_); name=(_, _, name)})} ->
            output module_ + output "::" + output name

// Converts a pattern match statement in Juniper to the appropriate representation in C++
and compilePattern (pattern : PosAdorn<Pattern>) (path : PosAdorn<Expr>) =
    let mutable conditions = []
    let mutable assignments = []
    let rec compilePattern' (pattern : PosAdorn<Pattern>) path : unit =
        match pattern with
            | (_, typ, MatchVar {varName=varName}) ->
                let varDec = InternalDeclareVar {varName=varName; typ=Option.map dummyWrap typ; right=path}
                assignments <- varDec::assignments
            | (_, _, MatchIntVal intLit) ->
                let check = BinaryOpExp {op=dummyWrap Equal; left=path; right=IntExp intLit |> dummyWrap}
                conditions <- check::conditions
            | (_, _, MatchFloatVal floatLit) ->
                let check = BinaryOpExp {op=dummyWrap Equal; left=path; right=FloatExp floatLit |> dummyWrap}
                conditions <- check::conditions
            | ((_, _, MatchValCon {name=name; innerPattern=innerPattern; id=Some index}) | (_, _, MatchValConModQualifier {modQualifier=(_, _, {name=name}); innerPattern=innerPattern; id=Some index})) ->
                let tag = RecordAccessExp {record=path; fieldName=dummyWrap "tag"}
                let check = BinaryOpExp {op=dummyWrap Equal; left=dummyWrap tag; right=(sprintf "%d" index) |> dummyWrap |> IntExp |> dummyWrap}
                let path' = RecordAccessExp {record=path; fieldName=name} |> dummyWrap
                compilePattern' innerPattern path'
                conditions <- check::conditions
            | ((_, _, MatchEmpty) | (_, _, MatchUnderscore)) -> ()
            | (_, _, MatchRecCon {fields=(_, _, fields)}) ->
                fields |> List.iter (fun (fieldName, fieldPattern) ->
                                        let path' = RecordAccessExp {record=path; fieldName=fieldName} |> dummyWrap
                                        compilePattern' fieldPattern path')
            | (_, _, MatchTuple (_, _, patterns)) ->
                patterns |> List.iteri (fun i pat ->
                                            let path' = RecordAccessExp {record=path; fieldName=dummyWrap ("e" + (sprintf "%d" (i + 1)))} |> dummyWrap
                                            compilePattern' pat path')
    compilePattern' pattern path
    let truth = dummyWrap (TrueExp (dummyWrap ()))
    let condition = List.foldBack (fun cond andString ->
                                    BinaryOpExp {op = dummyWrap LogicalAnd;
                                                 left = dummyWrap cond;
                                                 right = andString} |> dummyWrap) conditions truth
    (condition, assignments)
        
// Technically "compile expression"--converts an expression in Juniper to the C++ representation,
// but it encapsulates a ton of the conversions and is considered holistic for that reason.
and compile ((_, maybeTy, expr) : PosAdorn<Expr>) : string =
    match expr with
        | NullExp _ ->
            output "juniper::shared_ptr<void>(NULL)"
        // Convert inline C++ code from Juniper directly to C++
        | InlineCode (_, _, code) ->
            output "(([&]() -> " + compileType (BaseTy (dummyWrap TyUnit)) + " {" + newline() + indentId() +
            output code + newline() + output "return {};" + newline() + unindentId() +
            output "})())"
        | TrueExp _ ->
            output "true"
        | FalseExp _ ->
            output "false"
        | IntExp (_, _, num) ->
            output num
        | FloatExp (_, _, num) ->
            output num
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
        // A sequence is a set of expressions separated by semicolons inside parentheses, where the last exp
        // is returned
        | SequenceExp (_, _, sequence) ->
            let len = List.length sequence
            output "(([&]() -> " +
            compileType (Option.get maybeTy) +
            output " {" +
            newline() +
            indentId() +
            ((List.mapi (fun i seqElement ->
                let isLastElem = (i = len - 1)
                (match unwrap seqElement with
                    // Hit a let expression embedded in a sequence
                    | LetExp {left=left; right=right} ->
                        let varName = Guid.string()
                        let (condition, assignments) = compilePattern left (dummyWrap (VarExp {name=dummyWrap varName}))
                        compile (dummyWrap (InternalDeclareVar {varName=dummyWrap varName; typ=None; right=right})) + output ";" + newline() +
                        output "if (!(" + compile condition + output ")) {" + newline() + indentId() +
                        compile (getDeathExpr (BaseTy (dummyWrap TyUnit))) + output ";" + newline() + unindentId() +
                        output "}" + newline() +
                        (assignments |> List.map (fun expr -> compile (dummyWrap expr) + output ";" + newline()) |> String.concat "") +
                        (if isLastElem then
                            output "return " + compile (dummyWrap (VarExp {name=dummyWrap varName})) + output ";"
                        else
                            output "")
                    | _ ->
                        (if isLastElem then
                            output "return "
                        else
                            output "") +
                        compile seqElement + output ";") +
                newline()
            ) sequence) |> String.concat "") +
            unindentId() +
            output "})())"
        // Hit a let expression not embedded in a sequence
        // In this case the bindings are useless but the right side might still produce side effects
        // and the condition might fail
        | LetExp {left=left; right=right} ->
            let unitTy = TyUnit |> dummyWrap |> BaseTy
            let varName = Guid.string()
            let (condition, assignments) = compilePattern left (dummyWrap (VarExp {name=dummyWrap varName}))
            output "(([&]() -> " + compileType (Option.get maybeTy) + output " {" + indentId() + newline() +
            compile (dummyWrap (InternalDeclareVar {varName=dummyWrap varName; typ=None; right=right})) + output ";" + newline() +
            output "if (!(" + compile condition + output ")) {" + newline() + indentId() +
            compile (getDeathExpr unitTy) + output ";" + newline() + unindentId() +
            output "}" + newline() +
            output "return " + compile (dummyWrap (VarExp {name=dummyWrap varName})) + output ";" +
            unindentId() + newline() + output "})())"
        | AssignExp {left=(_, _, left); right=right; ref=(_, _, ref)} ->
            let (_, Some ty, _) = right
            output "(" +
            (if ref then
                output "*((" + compileType ty + "*) (" + compileLeftAssign left + output ".get()))"
            else
                compileLeftAssign left) +
            output " = " +
            compile right +
            output ")"
        | CallExp {func=func; args=(_, _, args)} ->
            compile func + output "(" +
            (args |> List.map compile |> String.concat ", ") +
            output ")"
        | UnitExp _ ->
            output "{}"
        | VarExp {name=name} ->
            output (unwrap name)
        | WhileLoopExp {condition=condition; body=body} ->
            output "(([&]() -> " +
            compileType (BaseTy (dummyWrap TyUnit)) +
            output " {" + newline() + indentId() +
            output "while (" + compile condition + ") {" + indentId() + newline() +
            compile body + output ";" + unindentId() + newline() + output "}" + newline() +
            output "return {};" + newline() +
            unindentId() +
            output "})())"
        // Case is used for pattern matching
        | CaseExp {on=(posOn, Some onTy, on); clauses=(_, _, clauses)} ->
            let ty = Option.get maybeTy
            let unitTy = BaseTy (dummyWrap TyUnit)
            let onVarName = Guid.string()
            let equivalentExpr =
                List.foldBack
                    (fun (pattern, executeIfMatched) ifElseTree ->
                        let (condition, assignments) = compilePattern pattern (VarExp {name=dummyWrap onVarName} |> wrapWithType onTy)
                        let assignments' = List.map (wrapWithType unitTy) assignments
                        let seq = SequenceExp (dummyWrap (List.append assignments' [executeIfMatched]))
                        IfElseExp {condition=condition; trueBranch=wrapWithType ty seq; falseBranch=ifElseTree} |> wrapWithType ty
                    ) clauses (getDeathExpr ty)
            let decOn = InternalDeclareVar {varName=dummyWrap onVarName; typ=dummyWrap onTy |> Some; right=(posOn, Some onTy, on)} |> wrapWithType unitTy
            compile (wrapWithType ty (SequenceExp (wrapWithType ty [decOn; equivalentExpr])))
        // Internal declarations are used only by the compiler, not the user, for hidden variables
        | InternalDeclareVar {varName=(_, _, varName); typ=typ; right=right} ->
            (match typ with
                | None -> output "auto"
                | Some (_, _, typ') -> compileType typ') +
            output " " + output varName + output " = " + compile right
        | TemplateApplyExp {func=func; templateArgs=(_, _, templateArgs)} ->
            compile func + compileTemplateApply templateArgs
        | BinaryOpExp {left=left; op=op; right=right} ->
            let opStr = match unwrap op with
                            | Add -> "+"
                            | BitwiseAnd -> "&"
                            | BitwiseOr -> "|"
                            | Divide -> "/"
                            | Equal -> "=="
                            | Greater -> ">"
                            | GreaterOrEqual -> ">="
                            | Less -> "<"
                            | LessOrEqual -> "<="
                            | LogicalAnd -> "&&"
                            | LogicalOr -> "||"
                            | Modulo -> "%"
                            | Multiply -> "*"
                            | NotEqual -> "!="
                            | Subtract -> "-"
                            | BitshiftLeft -> "<<"
                            | BitshiftRight -> ">>"
            output "(" + compile left + output " " + output opStr + output " " + compile right + output ")"
        | RecordAccessExp { record=record; fieldName=(_, _, fieldName)} ->
            output "(" + compile record + output ")." + output fieldName
        | LambdaExp {clause=(_, _, {returnTy=(_, _, returnTy); arguments=(_, _, args); body=body})} ->
            output "juniper::function<" + compileType returnTy + "(" + (args |> List.map (fst >> unwrap >> compileType) |> String.concat ",") + ")>(" +
            output "[=](" + (args |> List.map (fun (ty, name) -> compileType (unwrap ty) + output " " + output (unwrap name)) |> String.concat ", ") +
            output ") mutable -> " + compileType returnTy + output " { " + newline() +
            indentId() + output "return " + compile body + output ";" + unindentId() + newline() + output " })"
        | ModQualifierExp {module_=(_, _, module_); name=(_, _, name)} ->
            output module_ + "::" + name
        | ArrayLitExp (_, _, exprs) ->
            let (ArrayTy {valueType=(_, _, valueType); capacity=(_, _, capacity)}) = Option.get maybeTy
            output "(juniper::array<" + compileType valueType + output ", " + compileCap capacity + output "> { {" +
            (exprs |> List.map (fun expr -> compile expr) |> String.concat ", ") +
            output"} })"
        | ArrayMakeExp {typ=(_, _, typ); initializer=maybeInitializer} ->
            let (ArrayTy {valueType=(_, _, valueType); capacity=(_, _, capacity)}) = typ
            output "(juniper::array<" + compileType valueType + output ", " + compileCap capacity + output ">()" +
            (match maybeInitializer with
                 | Some initializer -> output ".fill(" + compile initializer + output ")"
                 | None -> output "") +
            output ")"
        | UnaryOpExp {op=(_, _, op); exp=exp} ->
            (match op with
                 | LogicalNot -> output "!"
                 | BitwiseNot -> output "~") + output "(" + compile exp + output ")"
        | ForLoopExp {typ=typ; varName=varName; start=start; direction=direction; end_=end_; body=body} ->
            let startName = Guid.string()
            let endName = Guid.string()
            output "(([&]() -> " +
            compileType (BaseTy (dummyWrap TyUnit)) +
            output " {" + newline() + indentId() +
            compileType (unwrap typ) + output " " + output startName + output " = " + compile start + output ";" + newline() +
            compileType (unwrap typ) + output " " + output endName + output " = " + compile end_ + output ";" + newline() +
            output "for (" + compileType (unwrap typ) + output " " + output (unwrap varName) + output " = " + output startName + output "; " +
            output (unwrap varName) + (match unwrap direction with
                                           | Upto -> output " <= "
                                           | Downto -> output " >= ") + output endName + output "; " +
            output (unwrap varName) + (match unwrap direction with
                                           | Upto -> output "++"
                                           | Downto -> output "--") + output ") {" + indentId() + newline() +
            compile body + output ";" + unindentId() + newline() +
            output "}" + newline() +
            output "return {};" + newline() +
            unindentId() +
            output "})())"
        | ArrayAccessExp {array=array; index=index} ->
            output "(" + compile array + output ")[" + compile index + "]"
        | RecordExp {recordTy=recordTy; templateArgs=templateArgs; initFields=initFields} ->
            let retName = Guid.string()
            let actualTy =
                match templateArgs with
                    | None -> unwrap recordTy
                    | Some args -> TyApply {tyConstructor=recordTy; args=args}
            output "(([&]() -> " + compileType actualTy + output "{" + newline() + indentId() +
            compileType actualTy + output " " + output retName + output ";" + newline() +
            (unwrap initFields |> List.map (fun (fieldName, fieldExpr) ->
                                                output retName + output "." + (unwrap fieldName |> output) + output " = " + compile fieldExpr + output ";" + newline()) |> String.concat "") +
            output "return " + output retName + output ";" + unindentId() + newline() + output "})())"
        | TupleExp exps ->
            output "(Prelude::tuple" + output (sprintf "%d" (List.length exps)) + output "<" +
            (exps |> List.map (fun (_, Some typ, _) -> compileType typ) |> String.concat ",") +
            output ">" + output "{" + (exps |> List.map compile |> String.concat ", ") + output "}" + output ")"
        | RefExp exp ->
            let (_, Some typ, _) = exp
            output "(juniper::shared_ptr<" + compileType typ + output ">(new " + compileType typ +
            output "(" + compile exp  + output ")))"
        | DerefExp exp ->
            output "(*((" + compile exp + output ").get()))"
        | DoWhileLoopExp {condition=condition; body=body} ->
            output "(([&]() -> " + indentId() + newline() +
            output "do {" + indentId() + newline() +
            compile body + unindentId() + newline() +
            output "} while(" + compile condition + output ");" + newline() +
            output "return {};" + unindentId() + newline() +
            output "})())"

// Convert Juniper template to C++ template
and compileTemplate (template : Template) : string = 
    let tyVars = template.tyVars |> unwrap |> List.map (unwrap >> (+) "typename ")
    let capVars = template.capVars |> unwrap |> List.map (unwrap >> (+) "int ")
    output "template<" +
    (List.append tyVars capVars |> String.concat ", " |> output) +
    output ">"

// Convert Juniper capacity values to C++ capacities (part of templates)
and compileCap (cap : CapacityExpr) : string =
    match cap with
        | CapacityNameExpr (_, _, name) ->
            name
        | CapacityOp { left=(_, _, left); op=(_, _, op); right=(_, _, right) } ->
            "(" + compileCap left + ")" +
            (match op with
                 | CAPPLUS -> "+"
                 | CAPMINUS -> "-"
                 | CAPMULTIPLY -> "*"
                 | CAPDIVIDE -> "/") +
            "(" + compileCap right + ")"
        | CapacityConst (_, _, constant) ->
            constant

// Convert Juniper template apply to C++ template apply
and compileTemplateApply (templateApp : TemplateApply) : string =
    output "<" +
    ((List.append
        (templateApp.tyExprs |> unwrap |> List.map (unwrap >> compileType))
        (templateApp.capExprs |> unwrap |> List.map (unwrap >> compileCap))) |> String.concat ", ") +
    output ">"

// Convert declarations in Juniper to C++ representations
// Includes modules use, function declarations, record declaration, let declarations, and unions.
and compileDec (dec : Declaration) : string =
    match dec with
        | (ExportDec _ | ModuleNameDec _) ->
            ""
        | OpenDec (_, _, openDecs) ->
            openDecs |> (List.map (fun (_, _, modName) ->
                output "using namespace " +
                output modName +
                output ";" +
                newline())) |> String.concat ""
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
            ((clause.arguments |> unwrap |>
                List.map (fun (ty, name) ->
                    (*let useReference = match unwrap ty with
                                           | BaseTy _ -> false
                                           | _ -> true
                    (if useReference then
                        output "const "
                    else
                        output "") +*)
                    (ty |> unwrap |> compileType) + //(if useReference then output "&" else output "") +
                    output " " + (name |> unwrap |> output))) |> String.concat ", ") +
            output ") {" +
            newline() +
            indentId() +
            output "return " +
            compile clause.body +
            output ";" +
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
                                                output ";" + newline())) |> (String.concat "")) +
            unindentId() +
            output "};"
        | LetDec {varName=(_, _, varName); typ=(_, _, typ); right=right} ->
            compileType typ +
            output " " +
            output varName +
            output " = " +
            compile right + output ";"
        | UnionDec { name=(_, _, name); valCons=(_, _, valCons); template=maybeTemplate } ->
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
            output "uint8_t tag;" +
            newline() +
            output "bool operator==(" + output name + output "& rhs) {" + newline() + indentId() +
            output "if (this->tag != rhs.tag) { return false; }" + newline() +
            output "switch (this->tag) {" + indentId() + newline() +
            (valCons |> List.mapi (fun i ((_, _, valConName), _) ->
                                       output (sprintf "case %d:" i) + newline() +
                                       indentId() + (sprintf "return this->%s == rhs.%s;" valConName valConName |> output) +
                                       unindentId() + newline()) |> String.concat "") +
            unindentId() + output "}" + newline() +
            output "return false;" + newline() +
            unindentId() + output "}" + newline() + newline() +
            output "bool operator!=(" + output name + output "&rhs) { return !(rhs == *this); }" + newline() +
            output "union {" +
            newline() +
            indentId() +
            (valCons |> List.map (fun ((_, _, valConName), maybeTy) ->
                (match maybeTy with
                    | None -> output "uint8_t"
                    | Some (_, _, ty) -> compileType ty) +
                output " " + valConName + output ";" + newline()) |> String.concat "") +
            unindentId() +
            output "};" +
            newline() +
            unindentId() +
            output "};" +
            newline() + newline() +
            // Output the function representation of the value constructor
            (valCons |> List.mapi (fun i ((_, _, valConName), maybeTy) ->
                (match maybeTemplate with
                    | Some (_, _, template) ->
                        compileTemplate template +
                        newline() +
                        compileType (TyApply {tyConstructor=dummyWrap (TyName (dummyWrap name));
                                              args=templateToTemplateApply template |> dummyWrap})
                    | None ->
                        compileType (TyName (dummyWrap name))) +
                output " " + output valConName + output "(" +
                (match maybeTy with
                     | None -> ""
                     | Some (_, _, ty) -> compileType ty + output " data") +
                output ") {" + newline() + indentId() +
                output "return {" + (sprintf "%d" i) + output ", " +
                (match maybeTy with
                     | None -> "0"
                     | Some _ -> "data") +
                output "};" + newline() +
                unindentId() + output "}" + newline() + newline()) |> String.concat "")

// Wrapper function for compiling the entire thing.
// Takes in list of modules, which each have their contributions to the AST, and translates them
// to the C++ representation.
and compileProgram (modList : Module list) : string =
    output "#include <inttypes.h>" + newline() +
    output "#include \"juniper.hpp\"" + newline() +
    output "#include <stdbool.h>" + newline() +
    output "#include <Arduino.h>" + newline() +
    output "#include <math.h>" + newline() + newline() +
    (modList |> List.map (fun (Module module_)->
        let moduleName = Module module_ |> Module.nameInModule |> unwrap
        output "namespace " + moduleName + output " {" + newline() +
        indentId() +
        (module_ |> List.map (fun (_, _, dec) ->
            match dec with
                | FunctionDec {name=(_, _, name)} when name = "main" ->
                    entryPoint <- Some {module_=dummyWrap moduleName; name=dummyWrap name}
                | _ -> ()
            compileDec dec + newline() + newline()) |> String.concat "") +
        unindentId() +
        output "}" + newline() + newline()) |> String.concat "") + newline() + newline() +
        (match entryPoint with
             | None ->
                 printfn "Unable to find program entry point. Please create a function called main."
                 failwith "Error"
             | Some {module_=(_, _, module_); name=(_, _, name)} ->
                 output "int main() {" + newline() + indentId() + output "init();" + newline() +
                 output module_ + output "::" + output name + output "();" + newline() +
                 output "return 0;" + unindentId() + newline() + "}")
