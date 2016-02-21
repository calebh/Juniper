module TypeChecker

open Ast

let nameInModule (Module decs) =
    let names = List.filter (fun dec -> match dec with
                                            | ModuleNameDec _ -> true
                                            | _ -> false) decs
    match names with
        | [ModuleNameDec name] -> name
        | [] -> failwith "Module name not found"
        | _ -> failwith "Multiple module names found in module"

let typesInModule (Module decs) = 
    let typeDecs = List.filter (fun dec -> match dec with
                                               | RecordDec _ -> true
                                               | UnionDec _  -> true
                                               | TypeAliasDec _ -> true
                                               | _ -> false) decs
    List.map (fun dec -> match dec with
                             | RecordDec {name=name} -> name
                             | UnionDec {name=name} -> name
                             | TypeAliasDec {name=name} -> name
                             | _ -> failwith "This should never happen") typeDecs

let opensInModule (Module decs) =
    let opens = List.filter (fun dec -> match dec with
                                            | OpenDec _ -> true
                                            | _ -> false) decs
    List.concat (List.map (fun dec -> match dec with
                             | OpenDec names -> names
                             | _ -> failwith "This should never happen") opens)

let qualifierWrap modName decName =
    {module_ = modName; name = decName}

let typecheck (modlist : Module list) =
    // Maps module qualifiers to type definitions
    let modQualToTypeDef = (List.fold (fun map (Module decs) ->
        let modName = nameInModule (Module decs)

        let typeDecs = List.filter (fun dec -> match dec with
                                                    | RecordDec _ -> true
                                                    | UnionDec _  -> true
                                                    | TypeAliasDec _ -> true
                                                    | _ -> false) decs
        List.fold (fun map2 dec ->
            let decName = match dec with
                                    | RecordDec {name=name} -> name
                                    | UnionDec {name=name} -> name
                                    | TypeAliasDec {name=name} -> name
                                    | _ -> failwith "This should never happen"
            let qual = qualifierWrap modName decName
            Map.add qual dec map2) map typeDecs
    ) Map.empty modlist)
    
    // Now build the type environments for every module
    // maps names to module qualifiers
    let tenvs0 = (List.map (fun (Module decs) ->
        let modName = nameInModule (Module decs)
        let names = typesInModule (Module decs)
        List.fold (fun map2 name ->
           Map.add name (qualifierWrap modName name) map2
        ) Map.empty names
    ) modlist)

    let modNamesToTenvs = Map.ofList (List.zip (List.map nameInModule modlist) tenvs0)

    let modNamesToAst = Map.ofList (List.zip (List.map nameInModule modlist) modlist)

    // Now deal with open declarations
    let tenvs1 = (Map.map (fun modName tenv0 ->
        let allOpens = opensInModule (Map.find modName modNamesToAst)
        List.fold (fun tenv1 nameToMerge ->
            MapExtensions.merge (Map.find nameToMerge modNamesToTenvs) tenv1 
        ) tenv0 allOpens
    ) modNamesToTenvs)

    printfn "%A" tenvs1

    ()