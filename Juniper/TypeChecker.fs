module TypeChecker

open Ast
open Microsoft.FSharp.Text.Lexing

let posString (p1 : Position, p2 : Position) : string = 
    sprintf "file %s, line %d column %d to line %d column %d" p1.FileName p1.Line p1.Column p2.Line p2.Column

let nameInModule (Module decs) =
    let names = List.filter (fun dec -> match dec with
                                            | (_, _, ModuleNameDec _) -> true
                                            | _ -> false) decs
    match names with
        | [((_, _), _, ModuleNameDec name)] -> name
        | [] -> failwith "Module name not found"
        | _ -> failwith "Multiple module names found in module"

let typesInModule (Module decs) = 
    let typeDecs = List.filter (fun dec -> match dec with
                                               | (_, _, RecordDec _) -> true
                                               | (_, _, UnionDec _ ) -> true
                                               | (_, _, TypeAliasDec _) -> true
                                               | _ -> false) decs
    List.map (fun dec -> match dec with
                             | (_, _, RecordDec {name=name}) -> name
                             | (_, _, UnionDec {name=name}) -> name
                             | (_, _, TypeAliasDec {name=name}) -> name
                             | _ -> failwith "This should never happen") typeDecs

let opensInModule (Module decs) =
    let opens = List.filter (fun dec -> match dec with
                                            | (_, _, OpenDec _) -> true
                                            | _ -> false) decs
    List.concat (List.map (fun dec -> match dec with
                                          | (_, _, OpenDec (_, _, names)) -> names
                                          | _ -> failwith "This should never happen") opens)

let exportsInModule (Module decs) =
    let exports = List.filter (fun dec -> match dec with
                                              | (_, _, ExportDec _) -> true
                                              | _ -> false) decs
    List.concat (List.map (fun dec -> match dec with
                                          | (_, _, ExportDec (_, _, names)) -> names
                                          | _ -> failwith "This should never happen") exports)

let declarationsInModule (Module decs) =
    let namedDecs = List.filter (fun dec -> match dec with
                                                | (_, _, FunctionDec _) -> true
                                                | (_, _, RecordDec _) -> true
                                                | (_, _, UnionDec _) -> true
                                                | (_, _, LetDec _) -> true
                                                | (_, _, TypeAliasDec _) -> true
                                                | _ -> false) decs
    List.map (fun dec -> match dec with
                             | (_, _, FunctionDec {name=name}) -> name
                             | (_, _, RecordDec {name=name}) -> name
                             | (_, _, UnionDec {name=name}) -> name
                             | (_, _, LetDec {varName=name}) -> name
                             | (_, _, TypeAliasDec {name=name}) -> name
                             | _ -> failwith "This should never happen") namedDecs

let valueDecsInModule (Module decs) =
    let namedDecs = List.filter (fun dec -> match dec with
                                                | (_, _, FunctionDec _) -> true
                                                | (_, _, LetDec _) -> true
                                                | _ -> false) decs
    List.map (fun dec -> match dec with
                             | (_, _, FunctionDec {name=name}) -> name
                             | (_, _, LetDec {varName=name}) -> name
                             | _ -> failwith "This should never happen") namedDecs

let qualifierWrap modName decName =
    {module_ = modName; name = decName}


let applyTemplate dec (substitutions : TyExpr list) =
    match dec with
        | FunctionDec {name=name; template=Some (_, _, Template {tyVars=(_, _, tyVars)}); returnTy=returnTy; clause=clause} ->
            let m = Map.ofList (List.zip (List.map unwrap tyVars) substitutions)
            let replace tyExpr =
                match tyExpr with
                    | ForallTy (_, _, name) -> Map.find name m
                    | x -> x
            FunctionDec {
                name = name;
                template = None
                returnTy = TreeTraversals.map1 replace returnTy
                clause = TreeTraversals.map1 replace clause
            }
        | x -> x
   


let eqTypes (ty1 : TyExpr) (ty2 : TyExpr) : bool = (ty1 = ty2)

let rec capacityString (cap : CapacityExpr) : string =
    match cap with
        | CapacityNameExpr (_, _, name) -> name
        | CapacityOp {left=(_, _, left); op=(_, _, op); right=(_, _, right)} ->
            let opStr = match op with
                            | CAPPLUS -> "+"
                            | CAPMINUS -> "-"
                            | CAPDIVIDE -> "/"
                            | CAPMULTIPLY -> "*"
            sprintf "%s %s %s" (capacityString left) opStr (capacityString right)
        | CapacityConst (_, _, name) -> name

let rec typeString (ty : TyExpr) : string =
    match ty with
        | BaseTy (_, _, baseTy) -> match baseTy with
                                    | TyUint8 -> "uint8"
                                    | TyUint16 -> "uint16"
                                    | TyUint32 -> "uint32"
                                    | TyUint64 -> "uint64"
                                    | TyInt8 -> "int8"
                                    | TyInt16 -> "int16"
                                    | TyInt32 -> "int32"
                                    | TyInt64 -> "int64"
                                    | TyBool -> "bool"
        | TyModuleQualifier {module_=(_, _, module_); name=(_, _, name)} -> sprintf "%s:%s" module_ name
        | TyName (_, _, name) -> name
        | TyApply {tyConstructor=(_, _, tyConstructor); args=(_, _, args)} ->
                sprintf "%s<%s>" (typeString tyConstructor) (String.concat "," (List.map (typeString << unwrap) args))
        | ArrayTy {valueType=(_, _, valueType); capacity=(_, _, capacity)} ->
                sprintf "%s[%s]" (typeString valueType) (capacityString capacity)
        | FunTy {args=(_, _, args); returnType=(_, _, returnType)} ->
                sprintf "((%s) -> %s)" (String.concat "," (List.map (typeString << unwrap) args)) (typeString returnType)
        | ForallTy (_, _, name) -> sprintf "'%s" name

(*
    denv => type module qualifiers to actual definition
    menv => type names to module qualifiers
    tenv => variable names to type module qualifiers
*)
let rec typeCheckExpr (denv : Map<ModQualifierRec, PosAdorn<Declaration>>)
                      (menv : Map<string, ModQualifierRec>)
                      (tenv : Map<string, ModQualifierRec>)
                      (expr : Expr)
                      : PosAdorn<Expr> =
    let tc = typeCheckExpr denv menv tenv
    match expr with
        | IfElseExp {condition=(posc, _, condition);
                     trueBranch=(post, _, trueBranch);
                     falseBranch=(posf, _, falseBranch)} ->
            // cCondition stands for type checked condition
            let (_, Some typec, cCondition) = tc condition
            let tbool = BaseTy (dummyWrap TyBool)
            if eqTypes typec tbool then
                let (_, Some typet, cTrueBranch) = tc trueBranch
                let (_, Some typef, cFalseBranch) = tc falseBranch
                if eqTypes typet typef then
                    wrapWithType
                        typet
                        (IfElseExp {condition = (posc, Some typec, cCondition);
                                    trueBranch = (post, Some typet, cTrueBranch);
                                    falseBranch = (posf, Some typef, cFalseBranch)})
                else
                    printfn "Type error in %s and %s: true branch of if statement has type %s and false branch has type %s. These types were expected to match." (posString post) (posString posf) (typeString typet) (typeString typef)
                    failwith "Type error"
            else
                printfn "Type error in %s: condition of if statement expected to have type %s" (posString posc) (typeString tbool)
                failwith "Type error"
        | x -> ((dummyPos, dummyPos), None, x)

// Finally we can typecheck each module!
let typecheckModule (Module decs) denv menv tenv : Module =
    let typeCheckExpr' = typeCheckExpr denv menv tenv
    Module (List.map (fun (pos, _, dec) ->
        (pos, None,
            match dec with
                | LetDec {varName=varName;
                          typ=typ;
                          right=(posr, _, right)} ->
                    let lhs = unwrap typ
                    let (_, Some rhs, cRight) = typeCheckExpr' right
                    if eqTypes lhs rhs then
                        LetDec {varName=varName;
                                typ=typ;
                                right=(posr, Some rhs, cRight)}
                    else
                        printfn "Type error in %s: The let declaration's left hand side type of %s did not match the right hand side type of %s" (posString pos) (typeString lhs) (typeString rhs)
                        failwith "Semantic error"
                | x -> x
                (*| FunctionDec {name=name; template=template; clause=clause; returnTy=returnTy} ->
                    ()
                | _ -> ()*)
        )
    ) decs)


let typecheckProgram (modlist : Module list) (fnames : string list) : Module list =
    // SEMANTIC CHECK: All modules contain exactly one module declaration
    let modNamesToAst =
        let names = (List.map (fun (module_, fname) -> try
                                                            unwrap (nameInModule module_)
                                                        with
                                                          | _ -> printfn "Semantic error in %s: The module does not contain exactly one module declaration." fname;
                                                                 failwith "Semantic error")
                        (List.zip modlist fnames))
        Map.ofList (List.zip names modlist)

    // SEMANTIC CHECK: Export declarations are all valid in every module
    List.iter (fun (module_, fname) ->
        let decs = Set.ofList (List.map unwrap (declarationsInModule module_))
        let exports = Set.ofList (List.map unwrap (exportsInModule module_))
        
        if Set.isSubset exports decs then
            ()
        else
            let modName = unwrap (nameInModule module_)
            let diff = String.concat "','" (Set.difference exports decs)
            printfn "Semantic error in %s: The module '%s' exports '%s' but these declarations could not be found in the module." fname modName diff
            failwith "Semantic error"
    ) (List.zip modlist fnames)

    // SEMANTIC CHECK: Type names in template declarations are unique
    (List.iter (fun (Module decs, fname) ->
        let checkTemplate (Template {tyVars=(tpos, _, tyVars); capVars=(cpos, _, capVars)}) =
            if ListExtensions.hasDuplicates tyVars then
                printfn "Semantic error in %s: Template contains duplicate definitions of a type parameter" (posString tpos)
                failwith "Semantic error"
            elif ListExtensions.hasDuplicates capVars then
                printfn "Semantic error in %s: Template contains duplicate definitions of a capacity parameter" (posString cpos)
                failwith "Semantic error"
            else
                ()
        (List.iter (fun (_, _, dec) ->
            match dec with
                | FunctionDec {template=Some template} -> checkTemplate (unwrap template)
                | UnionDec {template=Some template} -> checkTemplate (unwrap template)
                | TypeAliasDec {template=Some template} -> checkTemplate (unwrap template)
                | RecordDec {template=Some template} -> checkTemplate (unwrap template)
                | _ -> ()
        ) decs)
    ) (List.zip modlist fnames))

    // Maps module names to type environments
    // Each module environment maps names to module qualifiers
    let modNamesToMenvs =
        // Now build the type environments for every module
        // maps names to module qualifiers
        let menvs0 = (List.map (fun (Module decs) ->
            let modName = nameInModule (Module decs)
            let names = typesInModule (Module decs)
            List.fold (fun map2 name ->
                let (_, _, name2) = name
                Map.add name2 (qualifierWrap modName name) map2
            ) Map.empty names
        ) modlist)

        let modNamesToMenvs0 = Map.ofList (List.zip (List.map (nameInModule >> unwrap) modlist) menvs0)
        
        // Same as menvs0 except we filter out entries in the menv that
        // are not exported
        let modNamesToExportedMenvs = (Map.map (fun modName menv0 ->
            let allExports = Set.ofList (List.map unwrap (exportsInModule (Map.find modName modNamesToAst)))
            Map.filter (fun tyName qualifier -> Set.contains tyName allExports) menv0
        ) modNamesToMenvs0)

        // Merge the menvs together based on the open declarations
        (Map.map (fun modName menv0 ->
            let allOpens = List.map unwrap (opensInModule (Map.find modName modNamesToAst))
            List.fold (fun menv1 nameToMerge ->
                MapExtensions.merge (Map.find nameToMerge modNamesToExportedMenvs) menv1 
            ) menv0 allOpens
        ) modNamesToMenvs0)

    // Maps module qualifiers to type definitions
    let modQualToTypeDec = (List.fold (fun map (Module decs) ->
        let modName = nameInModule (Module decs)

        let typeDecs = List.filter (fun dec -> match dec with
                                                   | (_, _, RecordDec _) -> true
                                                   | (_, _, UnionDec _)  -> true
                                                   | (_, _, TypeAliasDec _) -> true
                                                   | _ -> false) decs
        List.fold (fun map2 dec0 ->
            // Replace all TyNames with the more precise TyModuleQualifier
            let dec1 = TreeTraversals.map1 (fun tyexpr -> match tyexpr with
                                                              | TyName (pos, _, name) ->
                                                                   let menv = Map.find (unwrap modName) modNamesToMenvs
                                                                   TyModuleQualifier (Map.find name menv)
                                                              | x -> x) dec0
            let decName = match dec1 with
                              | (_, _, RecordDec {name=name}) -> name
                              | (_, _, UnionDec {name=name}) -> name
                              | (_, _, TypeAliasDec {name=name}) -> name
                              | _ -> failwith "This should never happen"
            let qual = qualifierWrap modName decName
            Map.add qual dec1 map2) map typeDecs
    ) Map.empty modlist)

    // Maps module names to type environments
    // Each type environment maps variable names to type module qualifiers
    let modNamesToTenvs =
        // Now build the type environments for every module
        // maps names to module qualifiers
        let tenvs0 = (List.map (fun (Module decs) ->
            let modName = nameInModule (Module decs)
            let names = valueDecsInModule (Module decs)
            List.fold (fun map2 name ->
                let (_, _, name2) = name
                Map.add name2 (qualifierWrap modName name) map2
            ) Map.empty names
        ) modlist)

        let modNamesToTenvs0 = Map.ofList (List.zip (List.map (nameInModule >> unwrap) modlist) tenvs0)

        // Same as tenvs0 except we filter out entries in the tenv that
        // are not exported
        let modNamesToExportedTenvs = (Map.map (fun modName tenv0 ->
            let allExports = Set.ofList (List.map unwrap (exportsInModule (Map.find modName modNamesToAst)))
            Map.filter (fun tyName qualifier -> Set.contains tyName allExports) tenv0
        ) modNamesToTenvs0)

        // Merge the tenvs together based on the open declarations
        (Map.map (fun modName tenv0 ->
            let allOpens = List.map unwrap (opensInModule (Map.find modName modNamesToAst))
            List.fold (fun tenv1 nameToMerge ->
                MapExtensions.merge (Map.find nameToMerge modNamesToExportedTenvs) tenv1 
            ) tenv0 allOpens
        ) modNamesToTenvs0)
    
    (List.map (fun module_ ->
        let moduleName = unwrap (nameInModule module_)
        // denv menv tenv
        typecheckModule module_ modQualToTypeDec (Map.find moduleName modNamesToMenvs) (Map.find moduleName modNamesToTenvs)
    ) modlist)