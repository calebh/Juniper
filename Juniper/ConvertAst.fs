module ConvertAst
module A = Ast
module T = TypedAst
open Extensions
open Error

// This module converts between untyped AST representations and typed AST representations

let convertTemplate ({tyVars=(_, tyVars); capVars=maybeCapVars} : Ast.Template) =
    let t = List.map Ast.unwrap tyVars
    let c = Option.map Ast.unwrap maybeCapVars |> Option.toList |> List.concat |> List.map Ast.unwrap
    ({tyVars=t; capVars=c} : T.Template)

// The mapping parameter is used to convert explicitly given type variable parameter
// into a non-conflicting form
let rec convertType menv tyVarMapping capVarMapping (tau : Ast.TyExpr) : T.TyExpr =
    let ct = convertType menv tyVarMapping capVarMapping
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
    | Ast.FunTy {template=maybeTemplate; args=args; returnType=(_, returnType)} ->
        let returnType' = ct returnType
        let args' = List.map Ast.unwrap args
        T.ConApp (T.TyCon T.FunTy, returnType'::(List.map (Ast.unwrap >> ct) args), [])
    | Ast.ModuleQualifierTy {module_=(_, module_); name=(_, name)} ->
        T.TyCon <| T.ModuleQualifierTy {module_=module_; name=name}
    | Ast.NameTy (pos, name) ->
        match Map.tryFind name menv with
        | Some (module_, name) -> T.TyCon <| T.ModuleQualifierTy {module_=module_; name=name}
        | None -> raise (SemanticError ((errStr [pos] ("Unable to find type named " + name + " in the module environment")).Force()))
    | Ast.ParensTy (_, tau) ->
        ct tau
    | Ast.RefTy (_, tau) ->
        T.ConApp (T.TyCon T.RefTy, [ct tau], [])
    | Ast.TupleTy taus ->
        T.ConApp (T.TyCon T.TupleTy, List.map (Ast.unwrap >> ct) taus, [])
    | Ast.VarTy (_, name) ->
        Map.findDefault name (T.TyVar name) tyVarMapping

and convertCapacity capVarMapping (cap : Ast.CapacityExpr) : T.CapacityExpr =
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
