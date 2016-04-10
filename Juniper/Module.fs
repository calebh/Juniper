module Module

open Ast

// Takes in module's declarations and finds the name of the module
let nameInModule (Module decs) =
    let names = List.filter (fun dec -> match dec with
                                            | (_, _, ModuleNameDec _) -> true
                                            | _ -> false) decs
    match names with
        | [((_, _), _, ModuleNameDec name)] -> name
        | [] -> failwith "Module name not found"
        | _ -> failwith "Multiple module names found in module"

// Takes in module's declarations and finds the types in the module
let typesInModule (Module decs) = 
    let typeDecs = List.filter (fun dec -> match dec with
                                               | (_, _, RecordDec _) -> true
                                               | (_, _, UnionDec _ ) -> true
                                               | _ -> false) decs
    List.map (fun dec -> match dec with
                             | (_, _, RecordDec {name=name}) -> name
                             | (_, _, UnionDec {name=name}) -> name
                             | _ -> failwith "This should never happen") typeDecs

// Takes in module's declarations and finds the opens (of outher modules) in the module
let opensInModule (Module decs) =
    let opens = List.filter (fun dec -> match dec with
                                            | (_, _, OpenDec _) -> true
                                            | _ -> false) decs
    List.concat (List.map (fun dec -> match dec with
                                          | (_, _, OpenDec (_, _, names)) -> names
                                          | _ -> failwith "This should never happen") opens)

// Takes in module's declarations and finds the exports in the module
let exportsInModule (Module decs) =
    let exports = List.filter (fun dec -> match dec with
                                              | (_, _, ExportDec _) -> true
                                              | _ -> false) decs
    List.concat (List.map (fun dec -> match dec with
                                          | (_, _, ExportDec (_, _, names)) -> names
                                          | _ -> failwith "This should never happen") exports)

// Takes in module's declarations and finds the names of the declarations in the module
let declarationsInModule (Module decs) =
    let namedDecs = List.filter (fun dec -> match dec with
                                                | (_, _, FunctionDec _) -> true
                                                | (_, _, RecordDec _) -> true
                                                | (_, _, UnionDec _) -> true
                                                | (_, _, LetDec _) -> true
                                                | _ -> false) decs
    List.concat (List.map (fun dec -> match dec with
                                          | (_, _, FunctionDec {name=name}) -> [name]
                                          | (_, _, RecordDec {name=name}) -> [name]
                                          | (_, _, UnionDec {name=name; valCons=valCons}) ->
                                                name::(valCons |> unwrap |> List.map fst)
                                          | (_, _, LetDec {varName=name}) -> [name]
                                          | _ -> failwith "This should never happen") namedDecs)

// Takes in module's declarations and finds the value declaratin names in the module
let valueDecsInModule (Module decs) =
    let namedDecs = List.filter (fun dec -> match dec with
                                                | (_, _, FunctionDec _) -> true
                                                | (_, _, LetDec _) -> true
                                                | _ -> false) decs
    List.map (fun dec -> match dec with
                             | (_, _, FunctionDec {name=name}) -> name
                             | (_, _, LetDec {varName=name}) -> name
                             | _ -> failwith "This should never happen") namedDecs