module ConvertAst
module A = Ast
module T = TypedAst
open Extensions
open Error
open System
open TypedAst

// This module converts between untyped AST representations and typed AST representations

let convertTemplate (explicitKindEnv : Map<string, T.Kind>) ({tyVars=(_, tyVars)} : A.Template) : T.Template =
    tyVars |>
    List.map
        (Ast.unwrap >>
         (fun name ->
            match Map.tryFind name explicitKindEnv with
            | Some kind -> T.TyVar (name, kind)
            | None -> T.TyVar (name, T.Star)))

// The mapping parameter is used to convert explicitly given type variable parameter
// into a non-conflicting form
let rec convertType (menv : Map<string, string * string>) (kindEnv : Map<string * string, T.Kind>)
                    (explicitTyVarKindEnv : Map<string, T.Kind>) (tyVarMapping : Map<string, T.TyVar>)
                    (tau : A.TyExpr) : T.Qual<T.TyExpr, T.TyExpr> =
    let ct = convertType menv kindEnv explicitTyVarKindEnv tyVarMapping
    match tau with
    | A.ApplyTy {A.tyConstructor=(_, tyConstructor); args=(_, {tyExprs=(_, tyExprs)})} ->
        let (T.Qual (preds1, tyConstructor')) = ct tyConstructor
        let qualTyExprs' = List.map (A.unwrap >> ct) tyExprs
        let preds2 = qualTyExprs' |> List.map T.getQualPreds |> Set.unionMany
        let tyExprs' = List.map T.unwrapQual qualTyExprs'
        T.Qual (Set.union preds1 preds2, T.TApExpr (tyConstructor', tyExprs'))
    | A.ArrayTy {valueType=(_, valueType); capacity=(capacityPos, capacity)} ->
        let (T.Qual (preds1, valueType')) = ct valueType
        let (T.Qual (preds2, capacity')) = ct capacity
        let specialCapacityPred = T.IsIn ({T.module_="Prelude"; T.name="Nat"}, [capacity'], errStr [capacityPos] "Unable to find Prelude:Nat type class instance associated with this array capacity")
        let preds = Set.add specialCapacityPred (Set.union preds1 preds2)
        T.Qual (preds, T.tArray valueType' capacity')
    | Ast.BaseTy (_, tau) ->
        let baseTyCon' = (match tau with
                          | Ast.TyUint8 -> T.TyConUint8
                          | Ast.TyUint16 -> T.TyConUint16
                          | Ast.TyUint32 -> T.TyConUint32
                          | Ast.TyUint64 -> T.TyConUint64
                          | Ast.TyInt8 -> T.TyConInt8
                          | Ast.TyInt16 -> T.TyConInt16
                          | Ast.TyInt32 -> T.TyConInt32
                          | Ast.TyInt64 -> T.TyConInt64
                          | Ast.TyBool -> T.TyConBool
                          | Ast.TyDouble -> T.TyConDouble
                          | Ast.TyFloat -> T.TyConFloat
                          | Ast.TyPointer -> T.TyConPointer
                          | Ast.TyUnit -> T.TyConUnit
                          | Ast.TyString -> T.TyConString)
        T.Qual (Set.empty, T.TConExpr (T.TyCon (baseTyCon', T.Star)))
    | Ast.FunTy {template=maybeTemplate; args=args; returnType=(_, returnType)} ->
        let (T.Qual (preds1, returnType')) = ct returnType
        let qualArgs' = List.map (Ast.unwrap >> ct) args
        let preds2 = qualArgs' |> List.map T.getQualPreds |> Set.unionMany
        let args' = List.map T.unwrapQual qualArgs'
        T.Qual (Set.union preds1 preds2, T.tFun args' returnType')
    | Ast.ModuleQualifierTy {module_=(_, module_); name=(_, name)} ->
        let modQual' = {T.module_=module_; name=name}
        match Map.tryFind (module_, name) kindEnv with
        | Some kind -> T.Qual (Set.empty, T.tModuleQualifier modQual' kind)
        | None -> raise (InternalCompilerError (sprintf "Unable to find kind associated with %s" (modQualifierString modQual')))
    | Ast.NameTy (_, name) ->
        match Map.tryFind name menv with
        | Some (module_, _) ->
            let modQual' = {T.module_=module_; name=name}
            match Map.tryFind (module_, name) kindEnv with
            | Some kind -> T.Qual (Set.empty, T.tModuleQualifier modQual' kind)
            | None -> raise (InternalCompilerError (sprintf "Unable to find kind associated with %s" (modQualifierString modQual')))
        | None ->
            raise (InternalCompilerError (sprintf "Unable to find module associated with %s" name))
    | Ast.ParensTy (_, tau) ->
        ct tau
    | Ast.RefTy (_, tau) ->
        let (T.Qual (preds, tau')) = ct tau
        T.Qual (preds, T.tRef tau')
    | Ast.TupleTy taus ->
        let qualTaus' = List.map (Ast.unwrap >> ct) taus
        let preds = qualTaus' |> List.map T.getQualPreds |> Set.unionMany
        let taus' = List.map T.unwrapQual qualTaus'
        T.Qual (preds, T.tTuple taus')
    | Ast.VarTy (_, name) ->
        let tyVar =
            match Map.tryFind name tyVarMapping with
            | Some t ->
                t
            | None ->
                let kind = Map.findDefault name T.Star explicitTyVarKindEnv
                (T.TyVar (name, kind))
        T.Qual (Set.empty, T.TVarExpr tyVar)
    | A.NatNumTy n ->
        let rec buildType n' : T.TyExpr =
            if n' = 0L then
                T.tModuleQualifier {T.module_="Prelude"; name="zero"} T.Star
            else
                let innerType = buildType (n' - 1L)
                T.TApExpr (T.tModuleQualifier {T.module_="Prelude"; name="succ"} (T.kindFun 1), [innerType])
        let nAsType = buildType (A.unwrap n)
        let pred = T.IsIn ({T.module_="Prelude"; T.name="Nat"}, [nAsType], errStr [A.getPos n] "Unable to find Prelude:Nat type class instance associated with this natural number type literal. Are you using a non-standard Prelude?")
        T.Qual (Set.singleton pred, nAsType)

let convertPredicates (menv : Map<string, string * string>) (kindEnv : Map<string * string, T.Kind>)
                      (explicitTyVarKindEnv : Map<string, T.Kind>) (tyVarMapping : Map<string, T.TyVar>)
                      (predicates : List<A.PosAdorn<A.TypeclassPredApply>>) : Set<T.Pred<T.TyExpr>> =
    let ct = convertType menv kindEnv explicitTyVarKindEnv tyVarMapping
    predicates |>
    List.map
        (fun wrappedPred ->
            let {A.TypeclassPredApply.predName=predName; A.templateApply=templateApply} = A.unwrap wrappedPred
            let modQual =
                match A.unwrap predName with
                | Choice1Of2 name ->
                    match Map.tryFind name menv with
                    | Some (module_, _) -> {T.module_=module_; T.name=name}
                    | None ->
                        let msg = sprintf "Unable to find declaration corresponding to %s in module environment" name
                        raise (InternalCompilerError ((errStr [A.getPos predName] msg).Force()))
                | Choice2Of2 {Ast.ModQualifierRec.module_=module_; name=name} ->
                    {T.module_=A.unwrap module_; T.name=A.unwrap name}
            let { A.TemplateApply.tyExprs=tyExprArgs } = A.unwrap templateApply
            let tyExprArgsQual' = A.unwrap tyExprArgs |> List.map (A.unwrap >> ct)
            let preds = List.map T.getQualPreds tyExprArgsQual' |> Set.unionMany
            let tyExprArgs' = List.map T.unwrapQual tyExprArgsQual'
            let msg = errStr [A.getPos wrappedPred] "Unable to find type class instance associated with this predicate"
            Set.add (T.IsIn (modQual, tyExprArgs', msg)) preds) |>
    Set.unionMany

let convertQual (menv : Map<string, string * string>) (kindEnv : Map<string * string, T.Kind>)
                (explicitTyVarKindEnv : Map<string, T.Kind>) (tyVarMapping : Map<string, T.TyVar>)
                (predicates : List<A.PosAdorn<A.TypeclassPredApply>>) (tau : A.TyExpr) : T.Qual<T.TyExpr, T.TyExpr> =
    let preds1 = convertPredicates menv kindEnv explicitTyVarKindEnv tyVarMapping predicates
    let (Qual (preds2, tau')) = convertType menv kindEnv explicitTyVarKindEnv tyVarMapping tau
    T.Qual (Set.union preds1 preds2, tau')