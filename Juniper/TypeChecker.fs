module TypeChecker

open Ast


let nameInModule (Module decs) =
    let names = List.filter (fun dec -> match dec with
                                            | ((_, _), ModuleNameDec _) -> true
                                            | _ -> false) decs
    match names with
        | [((_, _), ModuleNameDec name)] -> name
        | [] -> failwith "Module name not found"
        | _ -> failwith "Multiple module names found in module"

let typesInModule (Module decs) = 
    let typeDecs = List.filter (fun dec -> match dec with
                                               | ((_, _), RecordDec _) -> true
                                               | ((_, _), UnionDec _ ) -> true
                                               | ((_, _), TypeAliasDec _) -> true
                                               | _ -> false) decs
    List.map (fun dec -> match dec with
                             | ((_, _), RecordDec {name=name}) -> name
                             | ((_, _), UnionDec {name=name}) -> name
                             | ((_, _), TypeAliasDec {name=name}) -> name
                             | _ -> failwith "This should never happen") typeDecs

let opensInModule (Module decs) =
    let opens = List.filter (fun dec -> match dec with
                                            | ((_, _), OpenDec _) -> true
                                            | _ -> false) decs
    List.concat (List.map (fun dec -> match dec with
                             | ((_, _), OpenDec ((_, _), names)) -> names
                             | _ -> failwith "This should never happen") opens)

let qualifierWrap modName decName =
    {module_ = modName; name = decName}

let typecheck (modlist : Module list) =
    // Maps module qualifiers to type definitions
    let modQualToTypeDec = (List.fold (fun map (Module decs) ->
        let modName = nameInModule (Module decs)

        let typeDecs = List.filter (fun dec -> match dec with
                                                    | ((_, _), RecordDec _) -> true
                                                    | ((_, _), UnionDec _)  -> true
                                                    | ((_, _), TypeAliasDec _) -> true
                                                    | _ -> false) decs
        List.fold (fun map2 dec ->
            let decName = match dec with
                                    | ((_, _), RecordDec {name=name}) -> name
                                    | ((_, _), UnionDec {name=name}) -> name
                                    | ((_, _), TypeAliasDec {name=name}) -> name
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
            let ((_, _), name2) = name
            Map.add name2 (qualifierWrap modName name) map2
        ) Map.empty names
    ) modlist)

    let modNamesToTenvs = Map.ofList (List.zip (List.map (nameInModule >> unwrap) modlist) tenvs0)

    let modNamesToAst = Map.ofList (List.zip (List.map (nameInModule >> unwrap) modlist) modlist)

    // Now deal with open declarations
    let tenvs1 = (Map.map (fun modName tenv0 ->
        let allOpens = opensInModule (Map.find modName modNamesToAst)
        List.fold (fun tenv1 ((_, _), nameToMerge) ->
            MapExtensions.merge (Map.find nameToMerge modNamesToTenvs) tenv1 
        ) tenv0 allOpens
    ) modNamesToTenvs)

    ()
