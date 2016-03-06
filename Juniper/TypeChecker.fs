module TypeChecker

open Ast
open Microsoft.FSharp.Text.Lexing
open System.IO

let posString (p1 : Position, p2 : Position) : string = 
    let inRange line column =
        let notInRange = line < p1.Line ||
                         line > p2.Line ||
                         (line = p1.Line && column < p1.Column) ||
                         (line = p2.Line && column >= p2.Column)
        not notInRange
    let badCode =
        if File.Exists p1.FileName then
            let lines = File.ReadAllLines p1.FileName
            let relevantLines = lines.[p1.Line .. p2.Line]
            let arrows = Array.create relevantLines.Length (Array.create 0 ' ')
            for line in p1.Line .. p2.Line do
                let line' = line - p1.Line
                let lineLength = relevantLines.[line'].Length
                let arrowLine = Array.create lineLength ' '
                Array.set arrows line' arrowLine
                for column in 0 .. lineLength - 1 do
                    if inRange line column then
                        Array.set arrowLine column '^'
            let flattenedArrows = List.ofArray arrows |> List.map System.String.Concat
            let final = List.zip (List.ofArray relevantLines) flattenedArrows |> List.map (fun (a,b) -> a+"\n"+b+"\n") |> System.String.Concat
            sprintf "\n\n%s\n" final
        else
            ""
    sprintf "file %s, line %d column %d to line %d column %d%s" p1.FileName (p1.Line+1) p1.Column (p2.Line+1) p2.Column badCode

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


(*let applyTemplate dec (substitions : TyExpr list) =
    match dec with
        | FunctionDec {template=Some template} ->
            
        | x -> x

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
        | x -> x*)
   
let rec eqCapacities (cap1 : CapacityExpr) (cap2 : CapacityExpr) : bool =
    match (cap1, cap2) with
        | (CapacityConst c1, CapacityConst c2) ->
                unwrap c1 = unwrap c2
        | (CapacityNameExpr c1, CapacityNameExpr c2) ->
                unwrap c1 = unwrap c2
        | (CapacityOp c1, CapacityOp c2) ->
                unwrap c1.op = unwrap c2.op &&
                eqCapacities (unwrap c1.left) (unwrap c2.left) &&
                eqCapacities (unwrap c1.right) (unwrap c2.right)
        | _ -> cap1 = cap2

let rec eqTypes (ty1 : TyExpr) (ty2 : TyExpr) : bool =
    match (ty1, ty2) with
        | (BaseTy (_, _, t1), BaseTy (_, _, t2)) ->
                t1 = t2
        | (TyModuleQualifier t1, TyModuleQualifier t2) ->
                unwrap t1.module_ = unwrap t2.module_ && unwrap t1.name = unwrap t2.name
        | (TyApply t1, TyApply t2) ->
                (eqTypes (unwrap t1.tyConstructor) (unwrap t2.tyConstructor)) &&
                List.forall2 eqTypes (unwrap t1.args |> List.map unwrap) (unwrap t2.args |> List.map unwrap)
        | (FunTy t1, FunTy t2) ->
                (eqTypes (unwrap t1.returnType) (unwrap t2.returnType)) &&
                (unwrap t1.tyVarArity) = (unwrap t2.tyVarArity) &&
                (unwrap t1.capVarArity) = (unwrap t2.capVarArity) &&
                List.forall2 eqTypes (List.map unwrap t1.args) (List.map unwrap t2.args)
        | (ForallTy _, _) -> true
        | (_, ForallTy _) -> true
        | (ArrayTy t1, ArrayTy t2) ->
                eqTypes (unwrap t1.valueType) (unwrap t2.valueType) &&
                eqCapacities (unwrap t1.capacity) (unwrap t2.capacity)
        | _ -> (ty1 = ty2)

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
                                    | TyUnit -> "unit"
        | TyModuleQualifier {module_=(_, _, module_); name=(_, _, name)} -> sprintf "%s:%s" module_ name
        | TyName (_, _, name) -> name
        | TyApply {tyConstructor=(_, _, tyConstructor); args=(_, _, args)} ->
                sprintf "%s<%s>" (typeString tyConstructor) (String.concat "," (List.map (typeString << unwrap) args))
        | ArrayTy {valueType=(_, _, valueType); capacity=(_, _, capacity)} ->
                sprintf "%s[%s]" (typeString valueType) (capacityString capacity)
        | FunTy {args=args; returnType=(_, _, returnType)} ->
                sprintf "((%s) -> %s)" (String.concat ", " (List.map (typeString << unwrap) args)) (typeString returnType)
        | ForallTy (_, _, name) -> sprintf "'%s" name

(*
    denv => type module qualifiers to actual definition
    menv => type names to module qualifiers
    tenv => variable names to types and a bool which tells
        if the variable is mutable
*)
let rec typeCheckExpr (denv : Map<ModQualifierRec, PosAdorn<Declaration>>)
                      (menv : Map<string, ModQualifierRec>)
                      (tenv : Map<string, bool * TyExpr>)
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
                printfn "Type error in %s: condition of if statement expected to have type %s but had type %s instead" (posString posc) (typeString tbool) (typeString typec)
                failwith "Type error"
        | SequenceExp {exps=(poss, _, exps)} ->
            let (pose, _, exp)::rest = exps
            let (_, Some typee, cExp) = tc exp
            // Notice that we're matching on the typechecked AST here
            let tc' = match cExp with
                          // The first element of the sequence is a let expression
                          // and it has introduced a new binding
                          | LetExp {varName=varName; mutable_=mutable_; typ=typ; right=right} ->
                                let (_, Some tr, _) = right
                                let tenv' = Map.add (unwrap varName) (unwrap mutable_, tr) tenv
                                typeCheckExpr denv menv tenv'
                          | _ -> tc
            let (seqType, cRest) =
                match rest with
                    // Last thing in the sequence
                    // so the type of the sequence is the type
                    // of the expression
                    | [] -> (typee, [])
                    // Not the last thing in the sequence
                    // so the type of the sequence is the type
                    // of the rest
                    | _ -> let (_, Some typer, SequenceExp {exps=(_, _, cRest)}) = tc' (SequenceExp {exps=dummyWrap rest})
                           (typer, cRest)
            (wrapWithType
                seqType
                (SequenceExp {
                    exps=(poss, Some seqType, (pose, Some typee, cExp)::cRest)
                }))
        // Hit a let expression that is not part of a sequence
        // In this case its binding is useless, but the right hand side might still
        // produce side effects
        | LetExp {varName=varName;
                  typ=typ;
                  right=(posr, _, right);
                  mutable_=mutable_} ->
            wrapWithType
                (BaseTy (dummyWrap TyUnit))
                (let (_, Some tr, cRight) = tc right
                 match typ with
                     | None -> ()
                     | Some typ' -> if eqTypes tr (unwrap typ') then
                                        ()
                                    else
                                        printfn ""
                                        failwith "Type error"
                 LetExp {
                    mutable_=mutable_;
                    varName=varName;
                    typ=typ;
                    right=(posr, Some tr, cRight)
                 })
        | VarExp {name=(posn, _, name)} ->
            let typ = match Map.tryFind name tenv with
                      | None ->
                            printfn "Error in %s: variable named %s could not be found" (posString posn) name
                            failwith "Error"
                      | Some (_, typ') -> typ'
            wrapWithType
                (typ)
                (VarExp {name=(posn, None, name)})
        | LambdaExp {clause=(posc, _, clause)} ->
            let args = unwrap clause.arguments |> List.map (fun (ty, name) -> (unwrap name, (false, unwrap ty)))
            let tenv' = tenv |> Map.map (fun name (mut, typ) -> (false, typ))
            let tenv'' = MapExtensions.merge tenv' (Map.ofList args)
            let tc' = typeCheckExpr denv menv tenv''
            let (posb, _, _) = clause.body
            let (posr, _, _) = clause.returnTy
            let (_, Some typeb, cBody) = tc' (unwrap clause.body)
            if eqTypes typeb (unwrap clause.returnTy) then
                ()
            else
                printfn "Type error in lambda expression: The return type %s in %s does not match the body type %s in %s." (unwrap clause.returnTy |> typeString) (posString posr) (typeString typeb) (posString posb)
                failwith "Type error"
            let argsTypes = unwrap clause.arguments |> List.unzip |> fst
            let lambdaType = FunTy {tyVarArity=dummyWrap 0;
                                    capVarArity=dummyWrap 0;
                                    args=argsTypes;
                                    returnType=clause.returnTy}
            wrapWithType
                lambdaType
                (LambdaExp {clause=(posc, None, {
                    returnTy=clause.returnTy;
                    arguments=clause.arguments;
                    body=(posb, Some typeb, cBody)
                })})
        | UnitExp (posu, _, ()) ->
            wrapWithType
                (BaseTy (dummyWrap TyUnit))
                (UnitExp (posu, None, ()))
        | IntExp (posi, _, number) ->
            wrapWithType
                (BaseTy (dummyWrap TyInt32))
                (IntExp (posi, None, number))
        | TrueExp (post, _, ()) ->
            wrapWithType
                (BaseTy (dummyWrap TyBool))
                (TrueExp (post, None, ()))
        | FalseExp (post, _, ()) ->
            wrapWithType
                (BaseTy (dummyWrap TyBool))
                (FalseExp (post, None, ()))
        | x -> ((dummyPos, dummyPos), None, x)

// Finally we can typecheck each module!
let typecheckModule (Module decs0) denv menv tenv : Module =
    let typeCheckExpr' = typeCheckExpr denv menv tenv
    // TRANSFORM: Begin by transforming all type names to the
    // more accurate module qualifier (ie, the absolute path to the type)
    let decs = (TreeTraversals.map1 (fun (tyExpr : TyExpr) ->
        match tyExpr with
            | TyName (pos, _, name) ->
                if Map.containsKey name menv then
                    TyModuleQualifier (Map.find name menv)
                else
                    printfn "Type error in %s: the type %s does not exist." (posString pos) name
                    failwith "Type error"
            | x -> x
    ) decs0)
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
                (*| FunctionDec {name=name; template=template; clause=clause; returnTy=returnTy} ->
                    ()*)
                | x -> x
        )
    ) decs)


let typecheckProgram (modlist0 : Module list) (fnames : string list) : Module list =
    // TRANSFORM: Transform empty sequences to a unit expression
    // TRANSFROM: Transform sequences with one expression to just that expression
    let modlist1 = (TreeTraversals.map1 (fun expr ->
        match expr with
            | SequenceExp { exps=(pos, ty, []) } -> UnitExp (pos, ty, ())
            //| SequenceExp { exps=(pos, ty, [exp]) } -> unwrap exp
            | x -> x
    ) modlist0)

    // SEMANTIC CHECK: All modules contain exactly one module declaration
    let modNamesToAst =
        let names = (List.map (fun (module_, fname) -> try
                                                            unwrap (nameInModule module_)
                                                        with
                                                          | _ -> printfn "Semantic error in %s: The module does not contain exactly one module declaration." fname;
                                                                 failwith "Semantic error")
                        (List.zip modlist1 fnames))
        Map.ofList (List.zip names modlist1)

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
    ) (List.zip modlist1 fnames)

    // SEMANTIC CHECK: Type names in template declarations are unique
    (List.iter (fun (Module decs, fname) ->
        let checkTemplate {tyVars=(tpos, _, tyVars); capVars=(cpos, _, capVars)} =
            let tyVars' = List.map unwrap tyVars
            let capVars' = List.map unwrap capVars
            if ListExtensions.hasDuplicates tyVars' then
                printfn "Semantic error in %s: Template contains duplicate definitions of a type parameter" (posString tpos)
                failwith "Semantic error"
            elif ListExtensions.hasDuplicates capVars' then
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
    ) (List.zip modlist1 fnames))

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
        ) modlist1)

        let modNamesToMenvs0 = Map.ofList (List.zip (List.map (nameInModule >> unwrap) modlist1) menvs0)
        
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

    let modlist2 =
        List.map
            (fun module_ ->
                let name = unwrap (nameInModule module_)
                let menv = Map.find name modNamesToMenvs
                // TRANSFORM: Begin by transforming all type names to the
                // more accurate module qualifier (ie, the absolute path to the type)
                (TreeTraversals.map1 (fun (tyExpr : TyExpr) ->
                    match tyExpr with
                        | TyName (pos, _, name) ->
                            if Map.containsKey name menv then
                                TyModuleQualifier (Map.find name menv)
                            else
                                printfn "Type error in %s: the type %s does not exist." (posString pos) name
                                failwith "Type error"
                        | x -> x
                ) module_))
            modlist1


    // Maps module qualifiers to type definitions
    // Also known as the denv
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
    ) Map.empty modlist2)

    // Maps module names to type environments
    // Each type environment maps variable names to type expressions
    let modNamesToTenvs =
        // Now build the type environments for every module
        // maps names to module qualifiers
        let tenvs0 = (List.map (fun (Module decs) ->
            let modName = nameInModule (Module decs)
            List.fold (fun map0 dec ->
                let getArities template =
                    match template with
                        | None -> (dummyWrap 0, dummyWrap 0)
                        | Some (_, _, template) ->
                            let (tpos, _, _) = template.tyVars
                            let (cpos, _, _) = template.capVars
                            ((tpos, None, List.length (unwrap template.tyVars)),
                                (cpos, None, List.length (unwrap template.capVars)))
                match unwrap dec with
                    | LetDec let_ ->
                        Map.add (unwrap let_.varName) (false, (unwrap let_.typ)) map0
                    | FunctionDec fun_ ->
                        let clause = unwrap fun_.clause
                        let args = clause.arguments |> unwrap |> List.unzip |> fst
                        let (tyVarArity, capVarArity) = getArities fun_.template
                        Map.add (unwrap fun_.name) (false, FunTy {tyVarArity=tyVarArity;
                                                                  capVarArity=capVarArity;
                                                                  returnType=clause.returnTy;
                                                                  args=args}) map0
                    // Type unions add their value constructors as functions
                    // to the type environment
                    | UnionDec union_ ->
                        let returnType = TyModuleQualifier {module_=modName; name=union_.name}
                        // Add all of the value constructors as functions
                        List.fold (fun map1 (conName, typs) ->
                            let (tyVarArity, capVarArity) = getArities union_.template
                            Map.add (unwrap conName) (false, FunTy {tyVarArity=tyVarArity;
                                                                    capVarArity=capVarArity;
                                                                    returnType=dummyWrap returnType;
                                                                    args=unwrap typs}) map1
                        ) map0 (unwrap union_.valCons)
                    | _ -> map0
            ) Map.empty decs
        ) modlist2)

        let modNamesToTenvs0 = Map.ofList (List.zip (List.map (nameInModule >> unwrap) modlist2) tenvs0)

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
    ) modlist2)