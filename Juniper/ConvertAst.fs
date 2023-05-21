﻿module ConvertAst
module A = Ast
module T = TypedAst
open Extensions
open Error
open Constraint

// This module converts between untyped AST representations and typed AST representations

let convertTemplate ({tyVars=(_, tyVars); capVars=maybeCapVars} : Ast.Template) =
    let t = List.map Ast.unwrap tyVars
    let c = Option.map Ast.unwrap maybeCapVars |> Option.toList |> List.concat |> List.map Ast.unwrap
    ({tyVars=t; capVars=c} : T.Template)

let rec convertCapacity capVarMapping (cap : Ast.CapacityExpr) : T.CapacityExpr =
    let convertCapacity = convertCapacity capVarMapping
    match cap with
    | Ast.CapacityConst (_, value) ->
        T.CapacityConst value
    | Ast.CapacityNameExpr (_, name) ->
        Map.findDefault name (T.CapacityVar name) capVarMapping
    | Ast.CapacityOp {left=(_, left); op=(_, op); right=(_, right)} ->
        let left' = convertCapacity left
        let right' = convertCapacity right
        let op' = match op with
                    | Ast.CapAdd -> T.CapAdd
                    | Ast.CapDivide -> T.CapDivide
                    | Ast.CapMultiply -> T.CapMultiply
                    | Ast.CapSubtract -> T.CapSubtract
        T.CapacityOp {left=left'; op=op'; right=right'}
    | Ast.CapacityUnaryOp {op=(_, op); term=(_, term)} ->
        let op' = match op with
                    | Ast.CapNegate -> T.CapNegate
        let term' = convertCapacity term
        T.CapacityUnaryOp {op=op'; term=term'}

let rec removeAliases (dtenv : Map<string * string, T.DeclarationTy>) (pos : FParsec.Position * FParsec.Position) (tau : T.TyExpr) =
    let removeAliases' = removeAliases dtenv pos
    match tau with
    | T.ConApp (T.TyCon (T.ModuleQualifierTy {module_=module_; name=name}), argsTau, argsCap) ->
        match Map.tryFind (module_, name) dtenv with
        | Some (T.AliasDecTy (tyVars, capVars, aliasTau)) ->
            if not (List.length tyVars = List.length argsTau) then
                raise <| TypeError ((errStr [pos] (sprintf "Error when expanding the alias declaration %s:%s. The number of type arguments passed to the alias was %d, but the alias expected %d arguments." module_ name (List.length argsTau) (List.length tyVars))).Force())
            else
                ()
            if not (List.length capVars = List.length argsCap) then
                raise <| TypeError ((errStr [pos] (sprintf "Error when expanding the alias declaration %s:%s. The number of capacity arguments passed to the alias was %d, but the alias expected %d arguments." module_ name (List.length argsCap) (List.length capVars))).Force())
            else
                ()
            let typeBinding = Map.ofList (List.zip tyVars argsTau)
            let capBinding = Map.ofList (List.zip capVars argsCap)
            let tau' = Constraint.tycapsubst typeBinding capBinding aliasTau
            removeAliases' tau'
        | _ ->
            T.ConApp (T.TyCon (T.ModuleQualifierTy {module_=module_; name=name}), List.map removeAliases' argsTau, argsCap)
    | T.TyCon (T.ModuleQualifierTy {module_=module_; name=name}) ->
        match Map.tryFind (module_, name) dtenv with
        | Some (T.AliasDecTy ([], [], aliasTau)) ->
            removeAliases' aliasTau
        | Some (T.AliasDecTy _) ->
            failwith "Internal compiler error. The alias had arguments, when we were not expecting arguments."
        | _ ->
            tau
    | T.ConApp (conTau, argsTau, argsCap) ->
        T.ConApp (removeAliases' conTau, List.map removeAliases' argsTau, argsCap)
    | T.RecordTy (maybePacked, fields) ->
        T.RecordTy (maybePacked, Map.map (fun _ value -> removeAliases' value) fields)
    | T.ClosureTy fields ->
        T.ClosureTy (Map.map (fun _ value -> removeAliases' value) fields)
    | _ ->
        tau

// The mapping parameter is used to convert explicitly given type variable parameter
// into a non-conflicting form
let convertType menv denv (dtenv : Map<string * string, T.DeclarationTy>) tyVarMapping capVarMapping (tau : Ast.PosAdorn<Ast.TyExpr>) : T.TyExpr =
    let rec convertType' (tau : Ast.TyExpr) : T.TyExpr =
        let ct = convertType'
        let convertCapacity = convertCapacity capVarMapping
        match tau with
        | Ast.ApplyTy {tyConstructor=(_, tyConstructor); args=(_, {tyExprs=(_, tyExprs); capExprs=(_, capExprs)})} ->
            T.ConApp (ct tyConstructor, List.map (Ast.unwrap >> ct) tyExprs, List.map (Ast.unwrap >> convertCapacity) capExprs)
        | Ast.ArrayTy {valueType=(_, valueType); capacity=(_, capacity)} ->
            T.ConApp (T.TyCon T.ArrayTy, [ct valueType], [convertCapacity capacity])
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
        | Ast.FunTy {closure=(_, closure); args=args; returnType=(_, returnType)} ->
            let closure' = ct closure
            let returnType' = ct returnType
            T.ConApp (T.TyCon T.FunTy, closure'::returnType'::(List.map (Ast.unwrap >> ct) args), [])
        | Ast.ModuleQualifierTy {module_=(_, module_); name=(_, name)} ->
            T.TyCon <| T.ModuleQualifierTy {module_=module_; name=name}
        | Ast.NameTy (pos, name) ->
            match AstAnalysis.resolveUserTyName menv denv name with
            | Some (module_, name) -> T.TyCon <| T.ModuleQualifierTy {module_=module_; name=name}
            | None -> Map.findDefault name (T.TyVar name) tyVarMapping
        | Ast.RefTy (_, tau) ->
            T.ConApp (T.TyCon T.RefTy, [ct tau], [])
        | Ast.TupleTy taus ->
            T.ConApp (T.TyCon T.TupleTy, List.map (Ast.unwrap >> ct) taus, [])
        | Ast.RecordTy (_, {packed=packed; fields=(_, fields)}) ->
            let fieldNames = fields |> List.map (fst >> Ast.unwrap)
            let fieldTaus = fields |> List.map (snd >> Ast.unwrap >> ct)
            let fieldOrder =
                if Option.isSome packed then
                    Some fieldNames
                else
                    None
            let fieldMap = List.zip fieldNames fieldTaus |> Map.ofList
            T.RecordTy (fieldOrder, fieldMap)
        | Ast.ClosureTy (_, fields) ->
            let fieldNames = fields |> List.map (fst >> Ast.unwrap)
            let fieldTaus = fields |> List.map (snd >> Ast.unwrap >> ct)
            let fieldMap = List.zip fieldNames fieldTaus |> Map.ofList
            T.ClosureTy fieldMap
        | Ast.UnderscoreTy _ ->
            freshtyvar ()
                
    let tau' = convertType' (Ast.unwrap tau)
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