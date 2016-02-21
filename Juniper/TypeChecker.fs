module TypeChecker

open Ast

(*
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

let qualifierWrap modName decName =
    {module_ = modName; name = decName}

let typecheck (modlist : Module list) = 
    let modNameToTypesInMod = List.fold (fun map modl ->
                                            let modName = nameInModule modl
                                            let wrap = List.map (qualifierWrap modName)
                                            Map.add modName (wrap <| typesInModule modl) map)
                                        Map.empty modlist
    modNameToTypesInMod
*)