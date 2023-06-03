module ConvertAst
module A = Ast
module T = TypedAst
open Extensions
open Error
open Constraint

// This module converts between untyped AST representations and typed AST representations

let convertTemplate ((post, templateVars) : Ast.Template) : T.Template =
    let templateVarsNames = templateVars |> List.map (fst >> A.unwrap) |> Set.ofList
    if List.length templateVars = Set.count templateVarsNames then
        templateVars |>
        List.map
            (function
            | ((_, varName), A.StarKind _) -> (varName, T.StarKind)
            | ((_, varName), A.IntKind _) -> (varName, T.IntKind))
    else
        raise <| SemanticError ((errStr [post] "Template contains duplicate named arguments.").Force())

let convertTemplateToChoice templateVars =
    templateVars |>
    List.map
        (function
        | (varName, T.StarKind) -> Choice1Of2 (T.TyVar varName)
        | (varName, T.IntKind) -> Choice2Of2 (T.CapacityVar varName))

let rec convertCapacity capVarMapping (cap : A.PosAdorn<Ast.TyExpr>) : T.CapacityExpr =
    let convertCapacity = convertCapacity capVarMapping
    match A.unwrap cap with
    | A.CapacityConst (_, value) ->
        T.CapacityConst value
    | A.NameTy (_, name) ->
        Map.findDefault name (T.CapacityVar name) capVarMapping
    | A.CapacityOp {left=left; op=(_, op); right=right} ->
        let left' = convertCapacity left
        let right' = convertCapacity right
        let op' = match op with
                    | Ast.CapAdd -> T.CapAdd
                    | Ast.CapDivide -> T.CapDivide
                    | Ast.CapMultiply -> T.CapMultiply
                    | Ast.CapSubtract -> T.CapSubtract
        T.CapacityOp {left=left'; op=op'; right=right'}
    | A.CapacityUnaryOp {op=(_, op); term=term} ->
        let op' =
            match op with
            | Ast.CapNegate -> T.CapNegate
        let term' = convertCapacity term
        T.CapacityUnaryOp {op=op'; term=term'}
    | _ ->
        raise <| SemanticError ((errStr [A.getPos cap] "Expecting a capacity expression but found a type expression instead.").Force())

let rec removeAliases (dtenv : Map<string * string, T.DeclarationTy>) (pos : FParsec.Position * FParsec.Position) (tau : T.TyExpr) =
    let removeAliases' = removeAliases dtenv pos
    let removeAliasesArgs args =
        args |>
        List.map
            (function
            | Choice1Of2 argTau -> Choice1Of2 (removeAliases' argTau)
            | Choice2Of2 capExpr -> Choice2Of2 capExpr)
    match tau with
    | T.ConApp ((T.ModuleQualifierTy {module_=module_; name=name}), args) ->
        match Map.tryFind (module_, name) dtenv with
        | Some (T.AliasDecTy (templateVars, aliasTau)) ->
            if not (List.length templateVars = List.length args) then
                raise <| SemanticError ((errStr [pos] (sprintf "Error when expanding the alias declaration %s:%s. The number of type arguments passed to the alias was %d, but the alias expected %d arguments." module_ name (List.length args) (List.length templateVars))).Force())
            else
                ()
            let varMappings =
                List.zip templateVars args |>
                List.map
                    (function
                    | ((templateVarName, T.StarKind), Choice1Of2 arg) ->
                        Choice1Of2 (templateVarName, arg)
                    | ((templateCapVarName, T.IntKind), Choice2Of2 capArg) ->
                        Choice2Of2 (templateCapVarName, capArg)
                    | _ ->
                        failwith "Internal compiler error when expanding type alias. The kinds of the declaration and the arguments do not match.")
            let (typeMappings, capMappings) = Choice.splitChoice2 varMappings
            let typeBinding = Map.ofList typeMappings
            let capBinding = Map.ofList capMappings
            let tau' = Constraint.tycapsubst typeBinding capBinding aliasTau
            removeAliases' tau'
        | _ ->
            T.ConApp ((T.ModuleQualifierTy {module_=module_; name=name}), removeAliasesArgs args)
    | T.TyCon (T.ModuleQualifierTy {module_=module_; name=name}) ->
        match Map.tryFind (module_, name) dtenv with
        | Some (T.AliasDecTy ([], aliasTau)) ->
            removeAliases' aliasTau
        | Some (T.AliasDecTy (template, _)) ->
            let numArguments = List.length template
            raise <| SemanticError ((errStr [pos] (sprintf "Error when expanding the alias declaration %s:%s. The alias expects %d argument(s), but none were given by the user." module_ name numArguments)).Force())
        | _ ->
            tau
    | T.ConApp (conTau, args) ->
        T.ConApp (conTau, removeAliasesArgs args)
    | T.RecordTy (maybePacked, fields) ->
        T.RecordTy (maybePacked, Map.map (fun _ value -> removeAliases' value) fields)
    | T.ClosureTy fields ->
        T.ClosureTy (Map.map (fun _ value -> removeAliases' value) fields)
    | _ ->
        tau

// The mapping parameter is used to convert explicitly given type variable parameter
// into a non-conflicting form
let convertType menv denv (dtenv : Map<string * string, T.DeclarationTy>) (tyVarMapping : Map<string, T.TyExpr>) (capVarMapping : Map<string, T.CapacityExpr>) (tau : Ast.PosAdorn<Ast.TyExpr>) : T.TyExpr =
    let rec convertType' (tau : Ast.PosAdorn<Ast.TyExpr>) : T.TyExpr =
        let ct = convertType'
        let convertCapacity = convertCapacity capVarMapping
        match A.unwrap tau with
        | Ast.ApplyTy {tyConstructor=(posc, _) as tyConstructor; args=(posa, (_, templateArgs))} ->
            let ({module_=module_; name=name} : T.ModQualifierRec) as modQual =
                match ct tyConstructor with
                | T.TyCon (T.ModuleQualifierTy modQual) -> modQual
                | _ -> raise <| SemanticError ((errStr [posc] "Constructor in type application was not an algebraic datatype or a type alias.").Force())
            // Check the kinds of the arguments passed to the type application
            let templateVarKinds = AstAnalysis.getArgKinds denv posc modQual
            if List.length templateVarKinds = List.length templateArgs then
                let templateArgs' =
                    List.zip templateVarKinds templateArgs |>
                    List.map
                        (function
                        | (A.StarKind _, arg) ->
                            ct arg |> Choice1Of2
                        | (A.IntKind _, arg) ->
                            convertCapacity arg |> Choice2Of2)
                T.ConApp (T.ModuleQualifierTy modQual, templateArgs')
            else
                raise <| SemanticError ((errStr [posa] (sprintf "The number of type arguments passed to the %s:%s type was %d, but the type expected %d arguments." module_ name (List.length templateArgs) (List.length templateVarKinds))).Force())
        | Ast.ArrayTy {valueType=valueType; capacity=capacity} ->
            T.arrayty (ct valueType) (convertCapacity capacity)
        | Ast.BaseTy (_, tau) ->
            T.TyCon <| T.BaseTy (match tau with
                                | Ast.TyUint8 -> T.TyUint8
                                | Ast.TyUint16 -> T.TyUint16
                                | Ast.TyUint32 -> T.TyUint32
                                | Ast.TyUint64 -> T.TyUint64
                                | Ast.TyInt8 -> T.TyInt8
                                | Ast.TyInt16 -> T.TyInt16
                                | Ast.TyInt32 -> T.TyInt32
                                | Ast.TyInt64 -> T.TyInt64
                                | Ast.TyBool -> T.TyBool
                                | Ast.TyDouble -> T.TyDouble
                                | Ast.TyFloat -> T.TyFloat
                                | Ast.TyPointer -> T.TyPointer
                                | Ast.TyUnit -> T.TyUnit
                                | Ast.TyString -> T.TyString
                                | Ast.TyRawPointer -> T.TyRawPointer)
        | Ast.FunTy {closure=closure; args=args; returnType=returnType} ->
            let closure' = ct closure
            let returnType' = ct returnType
            let args' = List.map ct args
            T.funty closure' returnType' args'
        | Ast.ModuleQualifierTy {module_=(_, module_); name=(_, name)} ->
            T.TyCon <| T.ModuleQualifierTy {module_=module_; name=name}
        | Ast.NameTy (pos, name) ->
            match AstAnalysis.resolveUserTyName menv denv name with
            | Some (module_, name) -> T.TyCon <| T.ModuleQualifierTy {module_=module_; name=name}
            | None -> Map.findDefault name (T.TyVar name) tyVarMapping
        | Ast.RefTy tau ->
            T.refty (ct tau)
        | Ast.TupleTy taus ->
            T.tuplety (List.map ct taus)
        | Ast.RecordTy (_, {packed=packed; fields=(_, fields)}) ->
            let fieldNames = fields |> List.map (fst >> Ast.unwrap)
            let fieldTaus = fields |> List.map (snd >> ct)
            let fieldOrder =
                if Option.isSome packed then
                    Some fieldNames
                else
                    None
            let fieldMap = List.zip fieldNames fieldTaus |> Map.ofList
            T.RecordTy (fieldOrder, fieldMap)
        | Ast.ClosureTy (_, fields) ->
            let fieldNames = fields |> List.map (fst >> Ast.unwrap)
            let fieldTaus = fields |> List.map (snd >> ct)
            let fieldMap = List.zip fieldNames fieldTaus |> Map.ofList
            T.ClosureTy fieldMap
        | Ast.UnderscoreTy _ ->
            freshtyvar ()
        | (A.CapacityConst _ | A.CapacityOp _ | A.CapacityUnaryOp _) ->
            raise <| SemanticError ((errStr [A.getPos tau] "Expecting a type expression but found a capacity expression instead.").Force())
                
    let tau' = convertType' tau
    let (pos, _) = tau
    removeAliases dtenv pos tau'

let convertInterfaceConstraint menv denv dtenv interfaceConstraint =
    match interfaceConstraint with
    | A.IsNum _ -> [T.IsNum]
    | A.IsInt _ -> [T.IsInt]
    | A.IsReal _ -> [T.IsReal]
    | A.HasFields (_, {packed=packed; fields=(_, fields)}) ->
        let cs1 =
            match packed with
            | Some _ -> [T.IsPacked]
            | None -> []
        let cs2 =
            fields |>
            List.map
                (fun ((_, name), tau) ->
                    T.HasField (name, convertType menv denv dtenv Map.empty Map.empty tau))
        T.IsRecord::(cs1 @ cs2)
    | A.IsPacked _ -> [T.IsPacked]

let convertToLHS expr=
    // Converts an expression into a valid left hand side (LHS) form
    let rec convertToLHSRec topLevel expr =
        let pose = A.getPos expr
        let expr' =
            match (A.unwrap expr) with
            | A.UnaryOpExp { op = (_, A.Deref); exp = exp} when topLevel ->
                A.RefMutation exp
            | A.RecordAccessExp { record = record; fieldName = fieldName } ->
                A.RecordMutation { record = convertToLHSRec false record; fieldName = fieldName }
            | A.RefRecordAccessExp {recordRef = recordRef; fieldName=fieldName } ->
                A.RefRecordMutation {recordRef = recordRef; fieldName=fieldName }
            | A.VarExp varName ->
                A.VarMutation varName
            | A.ModQualifierExp modQual ->
                A.ModQualifierMutation modQual
            | A.ArrayAccessExp { array = arr; index = index } ->
                A.ArrayMutation { array = convertToLHSRec false arr; index = index }
            | _ ->
                raise <| SemanticError ((errStr [pose] "The left hand side of the assignment operation contained an invalid expression.").Force())
        (pose, expr')
    convertToLHSRec true expr

let convertAssignOp op =
    match op with
    | Ast.Assign ->
        T.Assign
    | Ast.AddAssign ->
        T.AddAssign
    | Ast.SubAssign ->
        T.SubAssign
    | Ast.MulAssign ->
        T.MulAssign
    | Ast.DivAssign ->
        T.DivAssign
    | Ast.ModAssign ->
        T.ModAssign
    | Ast.BitwiseAndAssign ->
        T.BitwiseAndAssign
    | Ast.BitwiseOrAssign ->
        T.BitwiseOrAssign
    | Ast.BitwiseXorAssign ->
        T.BitwiseXorAssign
    | Ast.BitwiseLShiftAssign ->
        T.BitwiseLShiftAssign
    | Ast.BitwiseRShiftAssign ->
        T.BitwiseRShiftAssign