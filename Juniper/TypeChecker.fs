module TypeChecker

open Ast
open Microsoft.FSharp.Text.Lexing

let nameInModule (Module decs) =
    let names = List.filter (fun dec -> match dec with
                                            | (_, ModuleNameDec _) -> true
                                            | _ -> false) decs
    match names with
        | [((_, _), ModuleNameDec name)] -> name
        | [] -> failwith "Module name not found"
        | _ -> failwith "Multiple module names found in module"

let typesInModule (Module decs) = 
    let typeDecs = List.filter (fun dec -> match dec with
                                               | (_, RecordDec _) -> true
                                               | (_, UnionDec _ ) -> true
                                               | (_, TypeAliasDec _) -> true
                                               | _ -> false) decs
    List.map (fun dec -> match dec with
                             | (_, RecordDec {name=name}) -> name
                             | (_, UnionDec {name=name}) -> name
                             | (_, TypeAliasDec {name=name}) -> name
                             | _ -> failwith "This should never happen") typeDecs

let opensInModule (Module decs) =
    let opens = List.filter (fun dec -> match dec with
                                            | (_, OpenDec _) -> true
                                            | _ -> false) decs
    List.concat (List.map (fun dec -> match dec with
                                          | (_, OpenDec (_, names)) -> names
                                          | _ -> failwith "This should never happen") opens)

let exportsInModule (Module decs) =
    let exports = List.filter (fun dec -> match dec with
                                              | (_, ExportDec _) -> true
                                              | _ -> false) decs
    List.concat (List.map (fun dec -> match dec with
                                          | (_, ExportDec (_, names)) -> names
                                          | _ -> failwith "This should never happen") exports)

let declarationsInModule (Module decs) =
    let namedDecs = List.filter (fun dec -> match dec with
                                                | (_, FunctionDec _) -> true
                                                | (_, RecordDec _) -> true
                                                | (_, UnionDec _) -> true
                                                | (_, LetDec _) -> true
                                                | (_, TypeAliasDec _) -> true
                                                | _ -> false) decs
    List.map (fun dec -> match dec with
                             | (_, FunctionDec {name=name}) -> name
                             | (_, RecordDec {name=name}) -> name
                             | (_, UnionDec {name=name}) -> name
                             | (_, LetDec {varName=name}) -> name
                             | (_, TypeAliasDec {name=name}) -> name
                             | _ -> failwith "This should never happen") namedDecs

let valueDecsInModule (Module decs) =
    let namedDecs = List.filter (fun dec -> match dec with
                                                | (_, FunctionDec _) -> true
                                                | (_, LetDec _) -> true
                                                | _ -> false) decs
    List.map (fun dec -> match dec with
                             | (_, FunctionDec {name=name}) -> name
                             | (_, LetDec {varName=name}) -> name
                             | _ -> failwith "This should never happen") namedDecs

let qualifierWrap modName decName =
    {module_ = modName; name = decName}

let typecheckProgram (modlist : Module list) (fnames : string list) =
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

    // Maps module names to type environments
    // Each type environment maps names to module qualifiers
    let modNamesToTenvs =
        // Now build the type environments for every module
        // maps names to module qualifiers
        let tenvs0 = (List.map (fun (Module decs) ->
            let modName = nameInModule (Module decs)
            let names = typesInModule (Module decs)
            List.fold (fun map2 name ->
                let (_, name2) = name
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

    // Maps module qualifiers to type definitions
    let modQualToTypeDec = (List.fold (fun map (Module decs) ->
        let modName = nameInModule (Module decs)

        let typeDecs = List.filter (fun dec -> match dec with
                                                   | (_, RecordDec _) -> true
                                                   | (_, UnionDec _)  -> true
                                                   | (_, TypeAliasDec _) -> true
                                                   | _ -> false) decs
        List.fold (fun map2 dec0 ->
            // Replace all TyNames with the more precise TyModuleQualifier
            let dec1 = TreeTraversals.map1 (fun tyexpr -> match tyexpr with
                                                              | TyName (pos, name) ->
                                                                   let tenv = Map.find (unwrap modName) modNamesToTenvs
                                                                   TyModuleQualifier (Map.find name tenv)
                                                              | x -> x) dec0
            let decName = match dec1 with
                              | (_, RecordDec {name=name}) -> name
                              | (_, UnionDec {name=name}) -> name
                              | (_, TypeAliasDec {name=name}) -> name
                              | _ -> failwith "This should never happen"
            let qual = qualifierWrap modName decName
            Map.add qual dec1 map2) map typeDecs
    ) Map.empty modlist)

    // Maps module names to value environments
    // Each value environment maps names to type names
    let modNamesToVenvs =
        // Now build the value environments for every module
        // maps names to module qualifiers
        let venvs0 = (List.map (fun (Module decs) ->
            let modName = nameInModule (Module decs)
            let names = valueDecsInModule (Module decs)
            List.fold (fun map2 name ->
                let (_, name2) = name
                Map.add name2 (qualifierWrap modName name) map2
            ) Map.empty names
        ) modlist)

        let modNamesToVenvs0 = Map.ofList (List.zip (List.map (nameInModule >> unwrap) modlist) venvs0)

        // Same as venvs0 except we filter out entries in the venv that
        // are not exported
        let modNamesToExportedVenvs = (Map.map (fun modName venv0 ->
            let allExports = Set.ofList (List.map unwrap (exportsInModule (Map.find modName modNamesToAst)))
            Map.filter (fun tyName qualifier -> Set.contains tyName allExports) venv0
        ) modNamesToVenvs0)

        // Merge the venvs together based on the open declarations
        (Map.map (fun modName tenv0 ->
            let allOpens = List.map unwrap (opensInModule (Map.find modName modNamesToAst))
            List.fold (fun venv1 nameToMerge ->
                MapExtensions.merge (Map.find nameToMerge modNamesToExportedVenvs) venv1 
            ) tenv0 allOpens
        ) modNamesToVenvs0)
    ()

let eqTypes (ty1 : TyExpr) (ty2 : TyExpr) : bool = (ty1 = ty2)

let rec capacityString (cap : CapacityExpr) : string =
    match cap with
        | CapacityNameExpr (_, name) -> name
        | CapacityOp {left=(_,left); op=(_,op); right=(_,right)} ->
            let opStr = match op with
                            | CAPPLUS -> "+"
                            | CAPMINUS -> "-"
                            | CAPDIVIDE -> "/"
                            | CAPMULTIPLY -> "*"
            sprintf "%s %s %s" (capacityString left) opStr (capacityString right)

let rec typeString (ty : TyExpr) : string =
    match ty with
        | BaseTy (_, baseTy) -> match baseTy with
                                    | TyUint8 -> "uint8"
                                    | TyUint16 -> "uint16"
                                    | TyUint32 -> "uint32"
                                    | TyUint64 -> "uint64"
                                    | TyInt8 -> "int8"
                                    | TyInt16 -> "int16"
                                    | TyInt32 -> "int32"
                                    | TyInt64 -> "int64"
                                    | TyBool -> "bool"
        | TyModuleQualifier {module_=(_, module_); name=(_, name)} -> sprintf "%s:%s" module_ name
        | TyName (_, name) -> name
        | TyApply {tyConstructor=(_,tyConstructor); args=(_, args)} ->
                sprintf "%s<%s>" (typeString tyConstructor) (String.concat "," (List.map (typeString << unwrap) args))
        | ArrayTy {valueType=(_,valueType); capacity=(_,capacity)} ->
                sprintf "%s[%s]" (typeString valueType) (capacityString capacity)
        | FunTy {args=(_, args); returnType=(_,returnType)} ->
                sprintf "(%s) -> %s" (String.concat "," (List.map (typeString << unwrap) args)) (typeString returnType)

let posString (p1 : Position, p2 : Position) : string = 
    sprintf "file %s, line %d column %d to line %d column %d" p1.FileName p1.Line p1.Column p2.Line p2.Column

// Finally we can typecheck each module!
let typecheckModule (Module decs) tenv venv : unit =
    let typeOf' = typeOf tenv venv
    (List.iter (fun (pos, dec) ->
        match dec with
            | LetDec {varName=varName; typ=typ; right=right} ->
                let lhs = unwrap typ
                let rhs = typeOf' (unwrap right)
                if eqTypes lhs rhs then
                    ()
                else
                    printfn "Type error in %s: The let declaration's left hand side type of %s did not match the right hand side type of %s" (posString pos) (typeString lhs) (typeString rhs)
                    failwith "Semantic error"
            | FunctionDec {name=name; template=template; clause=clause; returnTy=returnTy} ->
                ()
            | _ -> ()
    ) decs)
    ()