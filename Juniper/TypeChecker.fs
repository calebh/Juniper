module TypeChecker

open Ast


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
    (*let modNamesToVenvs =
        let venvs0 = (List.map (fun (Module decs) ->
            let modName = nameInModule (Module decs)
            let valueDecs = List.filter (fun dec -> match dec with
                                                        | (_, FunctionDec _) -> true
                                                        | (_, LetDec _) -> true
                                                        | _ -> false) decs
        ) modlist)*)

    ()

let typecheckModule moduleAst tenv venv = ()