module Compiler
open System
open TypedAst
open Extensions

// The following are used for automatically adding new lines line indentation to transpiled C++
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

// In Juniper, quit is a templated function that calls exit(1)
// They are templated so they can be wrapped in a type so they can have return values consistent in typing
// with whatever statement or function they may be a part of (for example, a function that returns an int will
// return quit typed as an int, which will still exit the program).
let rec getQuitExpr (ty : TyExpr) : TyAdorn<Expr> =
    let quitFun = {module_="juniper"; name="quit"}
    let appliedQuit = TemplateApplyExp { func = Choice2Of2 quitFun;
                                         templateArgs = { tyExprs = [ty]; capExprs = []}} |> wrapWithType ty
    wrapWithType
        ty
        (CallExp {func = appliedQuit;
                  args = []})

// Converts type from Juniper representation to C++ representation.
and compileType theta kappa (ty : TyExpr) : string =
    let compileType = compileType theta kappa
    let compileCap = compileCap kappa
    match ty with
    | TyVar name ->
        match Map.tryFind name theta with
        | None -> name
        | Some ty' ->
            if ty = ty' then
                name
            else
                compileType ty'
    | ConApp (TyCon FunTy, returnType::args, _) ->
        output "juniper::function<" + compileType returnType + output "(" +
            (args |> List.map compileType |> String.concat ",")
            + output ")>"
    | ConApp (TyCon TupleTy, taus, _) ->
        output (sprintf "Prelude::tuple%d<" (List.length taus)) +
            (taus |> List.map compileType |> String.concat ",") +
            output ">"
    | ConApp (tyCon, taus, caps) ->
        output (compileType tyCon + "<" + ((List.append (List.map compileType taus) (List.map compileCap caps)) |> String.concat ", ") + ">")
    | TyCon tyc ->
        match tyc with
        | BaseTy bty ->
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
            | TyUnit -> output "juniper::unit"
            | TyDouble -> output "double"
            | TyPointer -> output "juniper::smartpointer"
            | TyString -> output "const char *"
        | ModuleQualifierTy {module_ = module_; name=name} ->
            output module_ +
            output "::" +
            output name
        | ArrayTy ->
            output "juniper::array"
        | RefTy ->
            output "juniper::shared_ptr"
        | FunTy ->
            failwith "This should never happen"

// Converts left side of a variable assignment to the C++ representation.
and compileLeftAssign theta kappa (left : LeftAssign) : string =
    let compileLeftAssign = compileLeftAssign theta kappa
    let compile = compile theta kappa
    match left with
    | VarMutation varName ->
        output varName
    | ArrayMutation {array=array; index=index} ->
        output "(" +
        compileLeftAssign array +
        output ")[" +
        compile index +
        output "]"
    | RecordMutation {record=record; fieldName=fieldName} ->
        output "(" +
        compileLeftAssign record +
        output ")." +
        output fieldName
    | ModQualifierMutation {module_=module_; name=name} ->
        output module_ + output "::" + output name

// Converts a pattern match statement in Juniper to the appropriate representation in C++
and compilePattern (pattern : TyAdorn<Pattern>) (path : TyAdorn<Expr>) =
    let mutable conditions = []
    let mutable assignments = []
    let rec compilePattern' (pattern : TyAdorn<Pattern>) path : unit =
        match pattern with
        | (_, typ, MatchVar {varName=varName}) ->
            let varDec = InternalDeclareVar {varName=varName; typ=typ; right=path}
            assignments <- varDec::assignments
        | (pos, _, MatchIntVal intLit) ->
            let check = BinaryOpExp {op=Equal; left=path; right=(pos, TyCon <| BaseTy TyInt32, IntExp intLit)}
            conditions <- check::conditions
        | (pos, _, MatchFloatVal floatLit) ->
            let check = BinaryOpExp {op=Equal; left=path; right=(pos, TyCon <| BaseTy TyFloat, FloatExp floatLit)}
            conditions <- check::conditions
        | (_, _, MatchValCon {modQualifier={module_=module_; name=name}; innerPattern=innerPattern; id=index}) ->
            let tag = RecordAccessExp {record=path; fieldName="tag"}
            let check = BinaryOpExp {op=Equal; left=dummyWrap tag; right=dummyWrap (IntExp <| int64 index)}
            let path' = RecordAccessExp {record=path; fieldName=name} |> dummyWrap
            match innerPattern with
            | Some p -> compilePattern' p path' |> ignore
            | None -> ()
            conditions <- check::conditions
        | (_, _, MatchUnderscore) -> ()
        | (_, _, MatchRecCon {fields=fields}) ->
            fields |> List.iter (fun (fieldName, fieldPattern) ->
                                    let path' = RecordAccessExp {record=path; fieldName=fieldName} |> dummyWrap
                                    compilePattern' fieldPattern path')
        | (_, _, MatchTuple patterns) ->
            patterns |> List.iteri (fun i pat ->
                                        let path' = RecordAccessExp {record=path; fieldName="e" + (sprintf "%d" (i + 1))} |> dummyWrap
                                        compilePattern' pat path')
    compilePattern' pattern path
    let truth = dummyWrap TrueExp
    let condition = List.foldBack (fun cond andString ->
                                    BinaryOpExp {op = LogicalAnd;
                                                 left = dummyWrap cond;
                                                 right = andString} |> dummyWrap) conditions truth
    (condition, assignments)

and compileDecRef d =
    match d with
    | Choice1Of2 name -> output name
    | Choice2Of2 {module_=module_; name=name} -> output module_ + output "::" + output name

// Technically "compile expression"--converts an expression in Juniper to the C++ representation,
// but it encapsulates a ton of the conversions and is considered holistic for that reason.
and compile theta kappa ((_, ty, expr) : TyAdorn<Expr>) : string =
    let compile = compile theta kappa
    let compileType = compileType theta kappa
    let compileCap = compileCap kappa
    let compileLeftAssign = compileLeftAssign theta kappa
    let unitty = TyCon <| BaseTy TyUnit
    match expr with
    | StringExp str ->
        output (sprintf "((const PROGMEM char *)(\"%s\"))" str)
    | QuitExp ty ->
        getQuitExpr ty |> compile
    | Smartpointer (name, body) ->
        output "(([&]() -> " +
        compileType ty +
        output " {" + newline() + indentId() +
        compileType (TyCon <| (BaseTy TyPointer)) + " " + name + ";" +
        output name + output ".destructorCallback = " + compile body + ";" + newline() +
        output "return " + name + ";" + newline() + unindentId() +
        output "})())"
    // Convert inline C++ code from Juniper directly to C++
    | InlineCode code ->
        output "(([&]() -> " + compileType (TyCon <| (BaseTy TyUnit)) + " {" + newline() + indentId() +
        output code + newline() + output "return {};" + newline() + unindentId() +
        output "})())"
    | TrueExp _ ->
        output "true"
    | FalseExp _ ->
        output "false"
    | IntExp num ->
        output (sprintf "%i" num)
    | FloatExp num ->
        output (sprintf "%f" num)
    | DoubleExp num ->
        output (sprintf "%f" num)
    | Int8Exp num ->
        output (sprintf "((int8_t) %i)" num)
    | UInt8Exp num ->
        output (sprintf "((uint8_t) %i)" num)
    | Int16Exp num ->
        output (sprintf "((int16_t) %i)" num)
    | UInt16Exp num ->
        output (sprintf "((uint16_t) %i)" num)
    | Int32Exp num ->
        output (sprintf "((int32_t) %i)" num)
    | UInt32Exp num ->
        output (sprintf "((uint32_t) %i)" num)
    | Int64Exp num ->
        output (sprintf "((int64_t) %i)" num)
    | UInt64Exp num ->
        output (sprintf "((uint64_t) %i)" num)
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
    | SequenceExp sequence ->
        let len = List.length sequence
        output "(([&]() -> " +
        compileType ty +
        output " {" +
        newline() +
        indentId() +
        ((List.mapi (fun i seqElement ->
            let isLastElem = (i = len - 1)
            (match unwrap seqElement with
                // Hit a let expression embedded in a sequence
                | LetExp {left=left; right=right} ->
                    let varName = Guid.string()
                    let (condition, assignments) = compilePattern left (dummyWrap (VarExp (varName, [], [])))
                    compile (dummyWrap (InternalDeclareVar {varName=varName; typ=getType right; right=right})) + output ";" + newline() +
                    output "if (!(" + compile condition + output ")) {" + newline() + indentId() +
                    compile (getQuitExpr (TyCon <| (BaseTy TyUnit))) + output ";" + newline() + unindentId() +
                    output "}" + newline() +
                    (assignments |> List.map (fun expr -> compile (dummyWrap expr) + output ";" + newline()) |> String.concat "") +
                    (if isLastElem then
                        output "return " + compile (dummyWrap (VarExp (varName, [], []))) + output ";"
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
        let unitTy = TyCon <| BaseTy TyUnit
        let varName = Guid.string()
        let (condition, assignments) = compilePattern left (dummyWrap (VarExp (varName, [], [])))
        output "(([&]() -> " + compileType ty + output " {" + indentId() + newline() +
        compile (dummyWrap (InternalDeclareVar {varName=varName; typ=ty; right=right})) + output ";" + newline() +
        output "if (!(" + compile condition + output ")) {" + newline() + indentId() +
        compile (getQuitExpr unitTy) + output ";" + newline() + unindentId() +
        output "}" + newline() +
        output "return " + compile (dummyWrap (VarExp (varName, [], []))) + output ";" +
        unindentId() + newline() + output "})())"
    | AssignExp {left=(_, _, left); right=right; ref=ref} ->
        let (_, ty, _) = right
        output "(" +
        (if ref then
            output "*((" + compileType ty + "*) (" + compileLeftAssign left + output ".get()))"
        else
            compileLeftAssign left) +
        output " = " +
        compile right +
        output ")"
    | CallExp {func=func; args=args} ->
        compile func + output "(" +
        (args |> List.map compile |> String.concat ", ") +
        output ")"
    | UnitExp _ ->
        output "juniper::unit()"
    | VarExp (name, [], []) ->
        output name
    | VarExp (name, t, c) ->
        let name' = output name
        let t' = List.map (Constraint.tycapsubst theta kappa >> compileType) t
        let c' = List.map (Constraint.capsubst kappa >> compileCap) c
        output name + output "<" + (t' @ c' |> String.concat ", ") + output ">"
    | WhileLoopExp {condition=condition; body=body} ->
        output "(([&]() -> " +
        compileType unitty +
        output " {" + newline() + indentId() +
        output "while (" + compile condition + ") {" + indentId() + newline() +
        compile body + output ";" + unindentId() + newline() + output "}" + newline() +
        output "return {};" + newline() +
        unindentId() +
        output "})())"
    // Case is used for pattern matching
    | CaseExp {on=(poso, onTy, on); clauses=clauses} ->
        let onVarName = Guid.string()
        let equivalentExpr =
            List.foldBack
                (fun (pattern, executeIfMatched) ifElseTree ->
                    let (condition, assignments) = compilePattern pattern (VarExp (onVarName, [], []) |> wrapWithType onTy)
                    let assignments' = List.map (wrapWithType unitty) assignments
                    let seq = SequenceExp (List.append assignments' [executeIfMatched])
                    IfElseExp {condition=condition; trueBranch=wrapWithType ty seq; falseBranch=ifElseTree} |> wrapWithType ty
                ) clauses (getQuitExpr ty)
        let decOn = InternalDeclareVar {varName=onVarName; typ=onTy; right=(poso, onTy, on)} |> wrapWithType unitty
        compile (wrapWithType ty (SequenceExp [decOn; equivalentExpr]))
    // Internal declarations are used only by the compiler, not the user, for hidden variables
    | InternalDeclareVar {varName=varName; typ=typ; right=right} ->
        output (compileType typ) + output " " + output varName + output " = " + output (compile right)
        //output "auto " + output varName + output " = " + output (compile right)
    | TemplateApplyExp {func=func; templateArgs=templateArgs} ->
        output (compileDecRef func) + output (compileTemplateApply theta kappa templateArgs)
    | BinaryOpExp {left=left; op=op; right=right} ->
        let opStr = match op with
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
                    | BitwiseXor -> "^"
        output "(" + compile left + output " " + output opStr + output " " + compile right + output ")"
    | RecordAccessExp { record=record; fieldName=fieldName} ->
        output "(" + compile record + output ")." + output fieldName
    | LambdaExp {returnTy=returnTy; arguments=args; body=body} ->
        output "juniper::function<" + compileType returnTy + "(" + (args |> List.map (snd >> compileType) |> String.concat ",") + ")>(" +
        output "[=](" + (args |> List.map (fun (name, ty) -> compileType ty + output " " + output name) |> String.concat ", ") +
        output ") mutable -> " + compileType returnTy + output " { " + newline() +
        indentId() + output "return " + compile body + output ";" + unindentId() + newline() + output " })"
    | ModQualifierExp ({module_=module_; name=name}, [], []) ->
        output module_ + "::" + output name
    | ModQualifierExp ({module_=module_; name=name}, t, c) ->
        let name' = output module_ + "::" + output name
        let t' = List.map (Constraint.tycapsubst theta kappa >> compileType) t
        let c' = List.map (Constraint.capsubst kappa >> compileCap) c
        output name' + output "<" + (t' @ c' |> String.concat ", ") + output ">"
    | ArrayLitExp exprs ->
        let (ConApp (TyCon ArrayTy, [valueType], [capacity])) = ty
        output "(juniper::array<" + compileType valueType + output ", " + compileCap capacity + output "> { {" +
        (exprs |> List.map (fun expr -> compile expr) |> String.concat ", ") +
        output"} })"
    | ArrayMakeExp {typ=typ; initializer=maybeInitializer} ->
        let (ConApp (TyCon ArrayTy, [valueType], [capacity])) = typ
        output "(juniper::array<" + compileType valueType + output ", " + compileCap capacity + output ">()" +
        (match maybeInitializer with
                | Some initializer -> output ".fill(" + compile initializer + output ")"
                | None -> output "") +
        output ")"
    | UnaryOpExp {op=op; exp=exp} ->
        match op with
        | Deref -> output "(*((" + compile exp + output ").get()))"
        | _ ->
            (match op with
            | Negate -> output "-"
            | LogicalNot -> output "!"
            | BitwiseNot -> output "~") + output "(" + compile exp + output ")"
    | ForLoopExp {typ=typ; varName=varName; start=start; direction=direction; end_=end_; body=body} ->
        let startName = Guid.string()
        let endName = Guid.string()
        output "(([&]() -> " +
        compileType unitty +
        output " {" + newline() + indentId() +
        compileType typ + output " " + output startName + output " = " + compile start + output ";" + newline() +
        compileType typ + output " " + output endName + output " = " + compile end_ + output ";" + newline() +
        output "for (" + compileType typ + output " " + output varName + output " = " + output startName + output "; " +
        output varName + (match direction with
                            | Upto -> output " <= "
                            | Downto -> output " >= ") + output endName + output "; " +
        output varName + (match direction with
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
        (*let actualTy =
            match templateArgs with
            | None -> unwrap recordTy
            | Some args -> TyApply {tyConstructor=recordTy; args=args}*)
        output "(([&]() -> " + compileType ty + output "{" + newline() + indentId() +
        compileType ty + output " " + output retName + output ";" + newline() +
        (initFields |> List.map (fun (fieldName, fieldExpr) ->
                                        output retName + output "." + output fieldName + output " = " + compile fieldExpr + output ";" + newline()) |> String.concat "") +
        output "return " + output retName + output ";" + unindentId() + newline() + output "})())"
    | TupleExp exps ->
        output "(Prelude::tuple" + output (sprintf "%d" (List.length exps)) + output "<" +
        (exps |> List.map (fun (_, typ, _) -> compileType typ) |> String.concat ",") +
        output ">" + output "{" + (exps |> List.map compile |> String.concat ", ") + output "}" + output ")"
    | RefExp exp ->
        let (_, typ, _) = exp
        output "(juniper::shared_ptr<" + compileType typ + output ">(new " + compileType typ +
        output "(" + compile exp  + output ")))"
    | DoWhileLoopExp {condition=condition; body=body} ->
        output "(([&]() -> " + indentId() + newline() +
        output "do {" + indentId() + newline() +
        compile body + output ";" + unindentId() + newline() +
        output "} while(" + compile condition + output ");" + newline() +
        output "return {};" + unindentId() + newline() +
        output "})())"

// Convert Juniper template to C++ template
and compileTemplate theta kappa (template : Template) : string =
    let tyVars =
        template.tyVars |>
        List.map (fun n ->
            let n' = match Constraint.tycapsubst theta kappa (TyVar n) with
                     | TyVar n' -> n'
                     | _ -> failwith "Internal compiler error: attempting to compile template where one of the template tyVars is not actully a tyVar"
            "typename " + n')
    let capVars =
        template.capVars |>
        List.map (fun n ->
            let (CapacityVar n') = Constraint.capsubst kappa (CapacityVar n)
            "int " + n')
    //let tyVars = template.tyVars |> List.map ((+) "typename ")
    //let capVars = template.capVars |> List.map ((+) "int ")
    output "template<" +
    (List.append tyVars capVars |> String.concat ", " |> output) +
    output ">"

// Convert Juniper capacity values to C++ capacities (part of templates)
and compileCap kappa (cap : CapacityExpr) : string =
    let compileCap = compileCap kappa
    match cap with
    | CapacityVar name ->
        match Map.tryFind name kappa with
        | None -> name
        | Some cap' -> compileCap cap'
    | CapacityOp { left=left; op=op; right=right } ->
        "(" + compileCap left + ")" +
        (match op with
        | CapAdd -> "+"
        | CapSubtract -> "-"
        | CapMultiply -> "*"
        | CapDivide -> "/") +
        "(" + compileCap right + ")"
    | CapacityConst constant ->
        sprintf "%i" constant
    | CapacityUnaryOp {op=op; term=term} ->
        (match op with
        | CapNegate -> "-") +
        "(" + compileCap term + ")"

// Convert Juniper template apply to C++ template apply
and compileTemplateApply theta kappa (templateApp : TemplateApply) : string =
    output "<" +
    ((List.append
        (templateApp.tyExprs |> List.map (compileType theta kappa))
        (templateApp.capExprs |> List.map (compileCap kappa))) |> String.concat ", ") +
    output ">"

and compileFunctionSignature theta kappa (FunctionDec {name=name; template=maybeTemplate; clause=clause}) =
    let compileType = compileType theta kappa
    (match maybeTemplate with
        | Some template ->
            compileTemplate theta kappa template +
            newline()
        | None ->
            output "") +
    (clause.returnTy |> compileType |> output) +
    output " " +
    output name +
    output "(" +
    ((clause.arguments |>
        List.map (fun (name, ty) ->
            (*let useReference = match unwrap ty with
                                    | BaseTy _ -> false
                                    | _ -> true
            (if useReference then
                output "const "
            else
                output "") +*)
            (compileType ty) + //(if useReference then output "&" else output "") +
            output " " + (name |> output))) |> String.concat ", ") +
    output ")"
    

// Convert declarations in Juniper to C++ representations
// Includes modules use, function declarations, record declaration, let declarations, and unions.
and compileDec module_ theta kappa (dec : Declaration) : string =
    let compile = compile theta kappa
    let compileType = compileType theta kappa
    let compileCap = compileCap kappa
    let compileLeftAssign = compileLeftAssign theta kappa
    match dec with
    //| InlineCodeDec (_, _, code) ->
        //output code
    | ModuleNameDec _ ->
        ""
    | IncludeDec inc ->
        inc |> List.map (fun i -> output "#include " + output i + newline()) |> String.concat ""
    | OpenDec openDecs ->
        openDecs |> (List.map (fun modName ->
            output "using namespace " +
            output modName +
            output ";" +
            newline())) |> String.concat ""
    | FunctionDec {name=name; template=maybeTemplate; clause=clause} ->
        compileFunctionSignature theta kappa dec + " {" +
        newline() +
        indentId() +
        output "return " +
        compile clause.body +
        output ";" +
        unindentId() +
        newline() +
        output "}"
    | RecordDec {name=name; fields=fields; template=maybeTemplate} ->
        (match maybeTemplate with
        | Some template ->
            compileTemplate theta kappa template +
            newline()
        | None ->
            output "") +
        output "struct " +
        output name +
        output " {" +
        newline() +
        indentId() +
        ((fields |> List.map (fun (fieldName, fieldTy) ->
                                 output (compileType fieldTy) +
                                 output " " +
                                 output fieldName +
                                 output ";" + newline())) |> (String.concat "")) +
        output "bool operator==(" + output name + output " rhs) {" + newline() + indentId() +
        output "return " +
        (fields |> List.map (fun (fieldName, fieldTy) ->
                                 output fieldName + output " == rhs." + output fieldName) |> List.cons2 (output "true") |> String.concat " && ") +
        output ";" + newline() + unindentId() +
        output "}" + newline() + newline() +
        output "bool operator!=(" + output name + output " rhs) {" + newline() + indentId() +
        output "return !(rhs == *this);" + unindentId() + newline() + output "}" +  unindentId() + newline() +
        output "};"
    | LetDec {varName=varName; right=right} ->
        compileType (getType right) +
        output " " +
        output varName +
        output " = " +
        compile right + output ";"
    | UnionDec { name=name; valCons=valCons; template=maybeTemplate } ->
        (match maybeTemplate with
            | Some template ->
                compileTemplate theta kappa template +
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
        output "bool operator==(" + output name + output " rhs) {" + newline() + indentId() +
        output "if (this->tag != rhs.tag) { return false; }" + newline() +
        output "switch (this->tag) {" + indentId() + newline() +
        (valCons |> List.mapi (fun i (valConName, _) ->
                                    output (sprintf "case %d:" i) + newline() +
                                    indentId() + (sprintf "return this->%s == rhs.%s;" valConName valConName |> output) +
                                    unindentId() + newline()) |> String.concat "") +
        unindentId() + output "}" + newline() +
        output "return false;" + newline() +
        unindentId() + output "}" + newline() + newline() +
        output "bool operator!=(" + output name + output " rhs) { return !(rhs == *this); }" + newline() +
        output "union {" +
        newline() +
        indentId() +
        (valCons |> List.map (fun (valConName, maybeTy) ->
            (match maybeTy with
                | None -> output "uint8_t"
                | Some ty -> output (compileType ty)) + output " " + valConName + output ";" + newline()) |> String.concat "") +
        unindentId() +
        output "};" +
        newline() +
        unindentId() +
        output "};" +
        newline() + newline() +
        // Output the function representation of the value constructor
        (valCons |> List.mapi (fun i (valConName, maybeTy) ->
            let retType =
                let m = TyCon <| ModuleQualifierTy {module_=module_; name=name}
                match maybeTemplate with
                | Some {tyVars=tyVars; capVars=capVars} ->
                    ConApp (m, List.map TyVar tyVars, List.map CapacityVar capVars)
                | None ->
                    m
            (match maybeTemplate with
            | Some template ->
                compileTemplate theta kappa template +
                newline() +
                compileType retType
            | None ->
                compileType retType) +
            output " " + output valConName + output "(" +
            (match maybeTy with
            | None -> ""
            | Some ty -> compileType ty + output " data") +
            output ") {" + newline() + indentId() +
            output "return (([&]() -> " + compileType retType + output " { " +
            compileType retType + output " ret; ret.tag = " + (sprintf "%d" i) + output "; " +
            output "ret." + output valConName + output " = " +
            (match maybeTy with
            | None -> output "0"
            | Some _ -> output "data") +
            output "; return ret; })());" + newline() +
            unindentId() + output "}" + newline() + newline()) |> String.concat "")

// Program: includes, types, values
//                              module names   opens                         v incudes           v mod name  v type dec           v mod    v fun/let dec v scc    v theta              v kappa
and compileProgram (program : string list * ((string * Declaration) list) * Declaration list * ((string * Declaration) list) * (((string * Declaration) list) * Map<string, TyExpr> * Map<string, CapacityExpr>) list) : string =
    let mutable entryPoint = None
    let executingDir = System.IO.Path.GetDirectoryName(System.Reflection.Assembly.GetExecutingAssembly().Location)
    let junCppStdPath = executingDir + "/cppstd/juniper.hpp"
    let junCppStd = System.IO.File.ReadAllText junCppStdPath
    let (moduleNames, opens, includes, typeDecs, valueSccs) = program
    (valueSccs |> List.iter (fun scc ->
        match scc with
        | (decs, _, _) ->
            decs |> List.iter (fun (module_, dec) ->
                match dec with
                | FunctionDec {name=name} when name = "main" ->
                    entryPoint <- Some {module_=module_; name=name}
                | _ -> ())
        | _ -> ()))
    let compileNamespace theta kappa (module_, dec) =
        output "namespace " + output module_ + output " {" + newline() + indentId() +
        compileDec module_ theta kappa dec + newline() + unindentId() +
        output "}" + newline() + newline()
    output "//Compiled on " + DateTime.Now.ToString() + newline() +
    output "#include <inttypes.h>" + newline() +
    output "#include <stdbool.h>" + newline() + newline() +
    junCppStd + newline() +
    (includes |> List.map (compileDec "" Map.empty Map.empty) |> String.concat "") + newline() +
    // Introduce all the namespaces
    (moduleNames |> List.map (fun name -> output "namespace " + output name + output " {}" + newline()) |> String.concat "") +
    // Now insert all the usings
    (opens |> List.map (compileNamespace Map.empty Map.empty) |> String.concat "") +
    (typeDecs |> List.map (compileNamespace Map.empty Map.empty) |> String.concat "") +
    // Compile forward declarations of all functions to enable recursion
    (valueSccs |> List.map (fun (decs, theta, kappa) ->
        decs |> 
        (List.filter (fun (_, dec) ->
            match dec with
            | FunctionDec _ -> true
            | _ -> false)) |>
        List.map (fun (module_, dec) ->
            output "namespace " + output module_ + output " {" + newline() + indentId() +
            compileFunctionSignature theta kappa dec + ";" + newline() + unindentId() +
            output "}" + newline() + newline()) |>
        String.concat ""
    ) |> String.concat "") +
    (valueSccs |> List.map (fun (decs, theta, kappa) ->
        decs |> List.map (compileNamespace theta kappa) |> String.concat "") |> String.concat "") +
    (match entryPoint with
    | None ->
        failwith "Unable to find program entry point. Please create a function called main."
    | Some {module_=module_; name=name} ->
        output "int main() {" + newline() + indentId() + output "init();" + newline() +
        output module_ + output "::" + output name + output "();" + newline() +
        output "return 0;" + unindentId() + newline() + "}")
