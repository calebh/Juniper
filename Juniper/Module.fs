module Module

// Takes in module's declarations and finds the name of the module
let nameInModule (Ast.Module decs) =
    let names = List.filter (fun dec -> match dec with
                                        | (_, Ast.ModuleNameDec _) -> true
                                        | _ -> false) decs
    match names with
        | [(_, Ast.ModuleNameDec name)] -> Some name
        | _ -> None
        
// Takes in module's declarations and finds the names of the declarations in the module
let declarationsInModule (Ast.Module decs) =
    let namedDecs = List.filter (fun dec -> match dec with
                                            | (_, Ast.FunctionDec _) -> true
                                            | (_, Ast.AliasDec _) -> true
                                            | (_, Ast.UnionDec _) -> true
                                            | (_, Ast.LetDec _) -> true
                                            | _ -> false) decs
    List.concat (List.map (fun dec -> match dec with
                                      | (_, Ast.FunctionDec {name=name}) -> [name]
                                      | (_, Ast.AliasDec {name=name}) -> [name]
                                      | (_, Ast.UnionDec {name=name; valCons=valCons}) ->
                                          name::(valCons |> Ast.unwrap |> List.map fst)
                                      | (_, Ast.LetDec {varName=name}) -> [name]
                                      | _ -> failwith "This should never happen") namedDecs) |> List.map Ast.unwrap

// Takes in module's declarations and finds the value declaratin names in the module
let valueDecsInModule (Ast.Module decs) =
    let namedDecs = List.filter (fun dec -> match dec with
                                            | (_, Ast.FunctionDec _) -> true
                                            | (_, Ast.LetDec _) -> true
                                            | _ -> false) decs
    List.map ((fun dec -> match dec with
                          | (_, Ast.FunctionDec {name=name}) -> name
                          | (_, Ast.LetDec {varName=name}) -> name
                          | _ -> failwith "This should never happen") >> Ast.unwrap) namedDecs

let isNamedDec dec = match dec with
                     | (Ast.AliasDec _ | Ast.UnionDec _ | Ast.LetDec _ | Ast.FunctionDec _) -> true
                     | _ -> false

// Takes in module's declarations and finds the types in the module
let typesInModule (Ast.Module decs) =
    let typeDecs = List.filter (fun dec -> match dec with
                                           | (_, Ast.AliasDec _) -> true
                                           | (_, Ast.UnionDec _ ) -> true
                                           | _ -> false) decs
    List.map ((fun dec -> match dec with
                         | (_, Ast.AliasDec {name=name}) -> name
                         | (_, Ast.UnionDec {name=name}) -> name
                         | _ -> failwith "This should never happen") >> Ast.unwrap) typeDecs

let opensInModule (Ast.Module decs) =
    let opens = List.filter (fun dec -> match Ast.unwrap dec with
                                        | Ast.OpenDec _ -> true
                                        | _ -> false) decs
    List.concat (List.map (fun dec -> match Ast.unwrap dec with
                                      |Ast.OpenDec names -> Ast.unwrap names
                                      | _ -> failwith "This 0should never happen") opens)

let nameOfDec dec = match dec with
                        | (Ast.AliasDec {name=name} | Ast.UnionDec {name=name} | Ast.LetDec {varName=name} | Ast.FunctionDec {name=name}) -> name
                        | _ -> failwith "This declaration doesn't have a name"

let isLet dec = match dec with
                | Ast.LetDec _ -> true
                | _ -> false
let isFunction dec = match dec with
                        | Ast.FunctionDec _ -> true
                        | _ -> false
let isInclude dec = match dec with
                    | Ast.IncludeDec _ -> true
                    | _ -> false
let isOpen dec = match dec with
                    | Ast.OpenDec _ -> true
                    | _ -> false
let isTypeDec dec = match dec with
                    | (Ast.UnionDec _ | Ast.AliasDec _) -> true
                    | _ -> false
let isUnionDec dec = match dec with
                     | Ast.UnionDec _ -> true
                     | _ -> false
let isInlineCodeDec dec = match dec with
                          | Ast.InlineCodeDec _ -> true
                          | _ -> false