module TypeChecker

// TODO: Prevent programmer from saving templated functions in variables

open Ast
open Microsoft.FSharp.Text.Lexing
open System.IO
open Extensions
open Module

let mutable alreadyCheckedFunctions : Set<ModQualifierRec * TemplateApply> = Set.empty

let addToAlreadyCheckedFunctions m t =
    alreadyCheckedFunctions <- Set.add (cleanAll m, cleanAll t) alreadyCheckedFunctions

let isAlreadyCheckedFunction m t =
    Set.contains (cleanAll m, cleanAll t) alreadyCheckedFunctions

let arithResultTy numTypel numTyper = 
    match (numTypel, numTyper) with
        | (x, y) when x=y -> x
        | (TyFloat,TyUint8) -> TyFloat
        | (TyFloat,TyUint16) -> TyFloat
        | (TyFloat,TyUint32) -> TyFloat
        | (TyFloat,TyUint64) -> TyFloat
        | (TyFloat,TyInt8) -> TyFloat
        | (TyFloat,TyInt16) -> TyFloat
        | (TyFloat,TyInt32) -> TyFloat
        | (TyFloat,TyInt64) -> TyFloat
        | (TyUint8,TyFloat) -> TyFloat
        | (TyUint8,TyUint16) -> TyUint16
        | (TyUint8,TyUint32) -> TyUint32
        | (TyUint8,TyUint64) -> TyUint64
        | (TyUint8,TyInt8) -> TyInt8
        | (TyUint8,TyInt16) -> TyInt16
        | (TyUint8,TyInt32) -> TyInt32
        | (TyUint8,TyInt64) -> TyInt64
        | (TyUint16,TyFloat) -> TyFloat
        | (TyUint16,TyUint8) -> TyUint16
        | (TyUint16,TyUint32) -> TyUint32
        | (TyUint16,TyUint64) -> TyUint64
        | (TyUint16,TyInt8) -> TyInt16
        | (TyUint16,TyInt16) -> TyInt16
        | (TyUint16,TyInt32) -> TyInt32
        | (TyUint16,TyInt64) -> TyInt64
        | (TyUint32,TyFloat) -> TyFloat
        | (TyUint32,TyUint8) -> TyUint32
        | (TyUint32,TyUint16) -> TyUint32
        | (TyUint32,TyUint64) -> TyUint64
        | (TyUint32,TyInt8) -> TyInt32
        | (TyUint32,TyInt16) -> TyInt32
        | (TyUint32,TyInt32) -> TyInt32
        | (TyUint32,TyInt64) -> TyInt64
        | (TyUint64,TyFloat) -> TyFloat
        | (TyUint64,TyUint8) -> TyUint64
        | (TyUint64,TyUint16) -> TyUint64
        | (TyUint64,TyUint32) -> TyUint64
        | (TyUint64,TyInt8) -> TyInt64
        | (TyUint64,TyInt16) -> TyInt64
        | (TyUint64,TyInt32) -> TyInt64
        | (TyUint64,TyInt64) -> TyInt64
        | (TyInt8,TyFloat) -> TyFloat
        | (TyInt8,TyUint8) -> TyInt8
        | (TyInt8,TyUint16) -> TyInt16
        | (TyInt8,TyUint32) -> TyInt32
        | (TyInt8,TyUint64) -> TyInt64
        | (TyInt8,TyInt16) -> TyInt16
        | (TyInt8,TyInt32) -> TyInt32
        | (TyInt8,TyInt64) -> TyInt64
        | (TyInt16,TyFloat) -> TyFloat
        | (TyInt16,TyUint8) -> TyInt16
        | (TyInt16,TyUint16) -> TyInt16
        | (TyInt16,TyUint32) -> TyInt32
        | (TyInt16,TyUint64) -> TyInt64
        | (TyInt16,TyInt8) -> TyInt16
        | (TyInt16,TyInt32) -> TyInt32
        | (TyInt16,TyInt64) -> TyInt64
        | (TyInt32,TyFloat) -> TyFloat
        | (TyInt32,TyUint8) -> TyInt32
        | (TyInt32,TyUint16) -> TyInt32
        | (TyInt32,TyUint32) -> TyInt32
        | (TyInt32,TyUint64) -> TyInt64
        | (TyInt32,TyInt8) -> TyInt32
        | (TyInt32,TyInt16) -> TyInt32
        | (TyInt32,TyInt64) -> TyInt64
        | (TyInt64,TyFloat) -> TyFloat
        | (TyInt64,TyUint8) -> TyInt64
        | (TyInt64,TyUint16) -> TyInt64
        | (TyInt64,TyUint32) -> TyInt64
        | (TyInt64,TyUint64) -> TyInt64
        | (TyInt64,TyInt8) -> TyInt64
        | (TyInt64,TyInt16) -> TyInt64
        | (TyInt64,TyInt32) -> TyInt64
        | _ -> failwith "Not a numerical type"

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

let qualifierWrap modName decName =
    {module_ = modName; name = decName}

let applyTemplate dec (substitutions : TemplateApply) =
    let replace tyMap capMap haystack =
        TreeTraversals.map2 (fun tyExpr -> match tyExpr with
                                               | ForallTy (_, _, name) -> Map.find name tyMap
                                               | x -> x)
                            (fun capExpr -> match capExpr with
                                                | CapacityNameExpr (_, _, name) -> Map.find name capMap
                                                | x -> x) haystack
    let tySubstitutions = substitutions.tyExprs |> unwrap |> List.map unwrap
    let capSubstitutions = substitutions.capExprs |> unwrap |> List.map unwrap
    match dec with
        | FunctionDec {name=name; template=Some (_, _, {tyVars=(_, _, tyVars); capVars=(_, _, capVars)}); clause=clause} ->
            // TODO: Better error message here when the zip fails

            // Notice that we don't substitute the capacities in here
            // This is because the only place where we need to use applyTemplate for
            // functions is when typechecking templated functions after types have
            // been substituted. Bad coding practice? Possibly... but it works
            let tyMap = Map.ofList (List.zip (List.map unwrap tyVars) tySubstitutions)
            let capMap = Map.ofList (List.zip (List.map unwrap capVars) capSubstitutions)
            FunctionDec {
                name = name;
                template = None;
                clause = TreeTraversals.map1 (fun tyExpr -> match tyExpr with
                                                                // TODO: Bug fix for when Map.find fails
                                                                | ForallTy (_, _, name) -> Map.find name tyMap
                                                                | x -> x) clause
            }
        | RecordDec {name=name; template=Some (_, _, {tyVars=(_, _, tyVars); capVars=(_, _, capVars)}); fields=fields} ->
            // TODO: Better error message here when the zip fails
            let tyMap = List.zip (List.map unwrap tyVars) tySubstitutions |> Map.ofList
            let capMap = List.zip (List.map unwrap capVars) capSubstitutions |> Map.ofList
            RecordDec {
                name=name;
                template=None;
                fields=replace tyMap capMap fields
            }
        | UnionDec {name=name; template=Some (_, _, {tyVars=(_, _, tyVars); capVars=(_, _, capVars)}); valCons=valCons} ->
            let tyMap = List.zip (List.map unwrap tyVars) tySubstitutions |> Map.ofList
            let capMap = List.zip (List.map unwrap capVars) capSubstitutions |> Map.ofList
            UnionDec {
                name = name;
                template = None;
                valCons = replace tyMap capMap valCons
            }
        | x -> x
   
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

let isIntType (ty : TyExpr) =
    match ty with
        | BaseTy (_, _, t1) ->
            match t1 with
                | (TyUint8 | TyUint16 | TyUint32 | TyUint64 | TyInt8 | TyInt16 | TyInt32 | TyInt64) -> true
                | _ -> false
        | ForallTy _ -> true
        | _ -> false

let isNumericalType (ty : TyExpr) =
    match ty with
        | BaseTy (_, _, t1) ->
            match t1 with
                | (TyUint8 | TyUint16 | TyUint32 | TyUint64 | TyInt8 | TyInt16 | TyInt32 | TyInt64 | TyFloat) -> true
                | _ -> false
        | ForallTy _ -> true
        | _ -> false

let rec eqTypes (ty1 : TyExpr) (ty2 : TyExpr) : bool =
    match (ty1, ty2) with
        | (x, y) when isNumericalType x && isNumericalType y -> true
        | (BaseTy (_, _, t1), BaseTy (_, _, t2)) ->
                t1 = t2
        | (TyModuleQualifier t1, TyModuleQualifier t2) ->
                unwrap t1.module_ = unwrap t2.module_ && unwrap t1.name = unwrap t2.name
        | (TyApply t1, TyApply t2) ->
                (eqTypes (unwrap t1.tyConstructor) (unwrap t2.tyConstructor)) &&
                List.forall2 eqTypes ((unwrap t1.args).tyExprs |> unwrap |> List.map unwrap) ((unwrap t2.args).tyExprs |> unwrap |> List.map unwrap) &&
                List.forall2 eqCapacities ((unwrap t1.args).capExprs |> unwrap |> List.map unwrap) ((unwrap t2.args).capExprs |> unwrap |> List.map unwrap)
        | (FunTy t1, FunTy t2) ->
                // Check that the return types are the same
                (eqTypes (unwrap t1.returnType) (unwrap t2.returnType)) &&
                (match (t1.template, t2.template) with
                    | (Some tv1, Some tv2) ->
                        // Check that the tyVar arities match
                        ((unwrap tv1).tyVars |> unwrap |> List.length) = ((unwrap tv2).tyVars |> unwrap |> List.length) &&
                        // Check that capVar arities match
                        ((unwrap tv1).tyVars |> unwrap |> List.length) = ((unwrap tv2).tyVars |> unwrap |> List.length)
                    | (None, None) -> true
                    | _ -> false) &&
                // Check that all the arguments are the same
                List.forall2 eqTypes (List.map unwrap t1.args) (List.map unwrap t2.args)
        | (ForallTy _, _) -> true
        | (_, ForallTy _) -> true
        | (ArrayTy t1, ArrayTy t2) ->
                eqTypes (unwrap t1.valueType) (unwrap t2.valueType) &&
                eqCapacities (unwrap t1.capacity) (unwrap t2.capacity)
        | (RefTy ty1, RefTy ty2) ->
                eqTypes (unwrap ty1) (unwrap ty2)
        | (TupleTy ty1, TupleTy ty2) ->
                List.forall2 eqTypes (List.map unwrap ty1) (List.map unwrap ty2)
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
                                    | TyFloat -> "float"
        | TyModuleQualifier {module_=(_, _, module_); name=(_, _, name)} -> sprintf "%s:%s" module_ name
        | TyName (_, _, name) -> name
        | TyApply {tyConstructor=(_, _, tyConstructor); args=(_, _, {tyExprs=(_, _, tyExprs); capExprs=(_, _, capExprs)})} ->
                let join = String.concat ","
                if List.length capExprs = 0 then
                    sprintf "%s<%s>" (typeString tyConstructor) (join (List.map (unwrap >> typeString) tyExprs))
                else
                    sprintf "%s<%s; %s>" (typeString tyConstructor) (join (List.map (unwrap >> typeString) tyExprs)) (join (List.map (unwrap >> capacityString) capExprs))
        | ArrayTy {valueType=(_, _, valueType); capacity=(_, _, capacity)} ->
                sprintf "%s[%s]" (typeString valueType) (capacityString capacity)
        | FunTy {template=maybeTemplate; args=args; returnType=(_, _, returnType)} ->
                let templateStr = match maybeTemplate with
                                      | None -> ""
                                      | Some (_, _, template) ->
                                            let tyVarStr = template.tyVars |> unwrap |> List.map unwrap |> List.map ((+) "'") |> String.concat ", "
                                            let capVarStr = template.capVars |> unwrap |> List.map unwrap |> String.concat ", "
                                            if capVarStr = "" then
                                                sprintf "<%s>" tyVarStr
                                            else
                                                sprintf "<%s; %s>" tyVarStr capVarStr
                sprintf "%s((%s) -> %s)" templateStr (String.concat ", " (List.map (unwrap >> typeString) args)) (typeString returnType)
        | ForallTy (_, _, name) -> sprintf "'%s" name
        | RefTy (_, _, ty) -> sprintf "%s ref" (typeString ty)
        | TupleTy tupleTys -> sprintf "(%s)" (List.map (unwrap >> typeString) tupleTys |> String.concat " * ")

// Prior to calling this function, it should be verified that funType actually
// has a template
let rec applyTemplateToFunctionType (funType : TyExpr) (template : TemplateApply) =
    let foo = typeString funType
    let (FunTy {template=Some (_, _, funTemplate); args=_; returnType=_}) = funType
    let templateTyVarsLen = template.tyExprs |> unwrap |> List.length
    let funTemplateTyVarsLen = funTemplate.tyVars |> unwrap |> List.length
    if templateTyVarsLen = funTemplateTyVarsLen then
        ()
    else
        printfn "%sType error: Function template's type arity is %d, but %d types were passed to the template." (template.tyExprs |> getPos |> posString) funTemplateTyVarsLen templateTyVarsLen
        failwith "Type error"
    let templateCapVarsLen = template.capExprs |> unwrap |> List.length
    let funTemplateCapVarsLen = funTemplate.capVars |> unwrap |> List.length
    if funTemplateCapVarsLen = templateCapVarsLen then
        ()
    else
        printfn "%sType error: Function template's capacity arity is %d, but %d capacities were passed to the template." (template.capExprs |> getPos |> posString) funTemplateCapVarsLen templateCapVarsLen
        failwith "Type error"
    let tyMap = List.zip (funTemplate.tyVars |> unwrap |> List.map unwrap) (template.tyExprs |> unwrap) |> Map.ofList
    let capMap = List.zip (funTemplate.capVars |> unwrap |> List.map unwrap) (template.capExprs |> unwrap) |> Map.ofList
    let (FunTy result) =
        (TreeTraversals.map2
            (fun (ty : TyExpr) ->
                match ty with
                    | ForallTy (_, _, name) ->
                        Map.find name tyMap |> unwrap
                    | x -> x)
            (fun (cap : CapacityExpr) ->
                match cap with
                    | CapacityNameExpr (_, _, name) ->
                        Map.find name capMap |> unwrap
                    | x -> x)
            funType)
    FunTy {result with template=None}

let toModuleQual (module_, name) =
    {module_=dummyWrap module_; name=dummyWrap name}

let toStringPair {module_=module_; name=name} =
    (unwrap module_, unwrap name)

let nameOfDec dec = match dec with
                        | (RecordDec {name=name} | UnionDec {name=name} | LetDec {varName=name} | FunctionDec {name=name}) -> name
                        | _ -> failwith "This declaration doesn't have a name"

let isNamedDec dec = match dec with
                         | (RecordDec _ | UnionDec _ | LetDec _ | FunctionDec _) -> true
                         | _ -> false

let isTypedDec dec = match dec with
                         | (LetDec _ | FunctionDec _) -> true
                         | _ -> false

(*
    denv => module qualifiers to actual declarations
    dtenv => module qualifiers to the type of declarations
    menv => type names to module qualifiers
    tenv => variable names to types and a bool which tells
        if the variable is mutable
*)
let rec typeCheckExpr (denv : Map<string * string, PosAdorn<Declaration>>)
                      (dtenv : Map<string * string, TyExpr>)
                      (tenv : Map<string, bool * TyExpr>)
                      (modNamesToTenvs : Map<string,Map<string,(bool * TyExpr)>>)
                      (capEnv : Set<string>)
                      (expr : Expr)
                      : PosAdorn<Expr> =
    let tc = typeCheckExpr denv dtenv tenv modNamesToTenvs capEnv

    let rec checkPattern (pattern : Pattern) (path : Expr) : (PosAdorn<Pattern> * Map<string, bool*TyExpr>) =
        let mutable tenv' = tenv
        let rec checkPattern' (pattern : Pattern) (path : Expr) : PosAdorn<Pattern> =
            let (_, Some pathTy, _) = tc path
            let pattern' = 
                match pattern with
                    | MatchEmpty -> dummyWrap MatchEmpty
                    | MatchUnderscore -> dummyWrap MatchUnderscore
                    | MatchVar {varName=varName; mutable_=mutable_; typ=tyConstraint} ->
                        match tyConstraint with
                            | Some (posTyConstraint, _, ty) when not (eqTypes pathTy ty) ->
                                printfn "%sType error: Type constraint given in pattern does not match the type of expression being matched on." (posString posTyConstraint)
                                failwith "Type error"
                            | _ ->
                                tenv' <- Map.add (unwrap varName) (unwrap mutable_, pathTy) tenv'
                                wrapWithType
                                    pathTy
                                    (MatchVar {varName=varName; mutable_=mutable_; typ=tyConstraint})
                    | MatchIntVal (posn, _, num) ->
                        if isIntType pathTy then
                            wrapWithType
                                pathTy
                                (MatchIntVal (posn, None, num))
                        else
                            printfn "%sType error: Integer type constraint given in pattern does not match the type of the expression being matched upon." (posString posn)
                            failwith "Type error"
                    | MatchFloatVal (posn, _, num) ->
                        let floatTy = BaseTy (dummyWrap TyFloat)
                        if eqTypes floatTy pathTy then
                            wrapWithType
                                pathTy
                                (MatchIntVal (posn, None, num))
                        else
                            printfn "%sType error: Float type constraint given in pattern does not match the type of the expression being matched upon." (posString posn)
                            failwith "Type error"
                    | MatchTuple (post, _, tuple) ->
                        let tuple' = (List.mapi (fun index (_, _, subPattern) ->
                                            checkPattern' subPattern (RecordAccessExp {
                                                                    record=dummyWrap path;
                                                                    fieldName=dummyWrap (sprintf "e%d" index)})
                                        ) tuple)
                        dummyWrap (MatchTuple (post, None, tuple'))
                    | MatchRecCon {typ=(posRecTy, _, recTy); fields=(posFieldList, _, fieldList)} ->
                        if eqTypes recTy pathTy then
                            let fieldList' = (List.map (fun ((posFieldName, _, fieldName), (posFieldPattern, _, fieldPattern)) ->
                                let path' = RecordAccessExp { record = dummyWrap path;
                                                              fieldName = (posFieldName, None, fieldName)}
                                let fieldPattern' = checkPattern' fieldPattern path'
                                ((posFieldName, None, fieldName), fieldPattern')
                            ) fieldList)
                            MatchRecCon {typ=(posRecTy, None, recTy); fields=(posFieldList, None, fieldList')} |> dummyWrap
                        else
                            printfn "%sType error: Record type given in pattern does not match the type of the expression being matched upon." (posString posRecTy)
                            failwith "Type error"
                    | (MatchValConModQualifier {modQualifier=(_, _, {name=(posn, _, name)}); template=maybeTemplate; innerPattern=(posValConPattern, _, valConPattern)}
                        | MatchValCon {name=(posn, _, name); template=maybeTemplate; innerPattern=(posValConPattern, _, valConPattern)} ) ->
                        // Value constructors are implemented as functions so
                        // the return type of the function should be the type
                        // we need

                        // TODO: What if the programmer pattern matches on a function instead
                        // of a value constructor. From the type alone there is no way to tell
                        // if the programmer is being honest
                        let ty =
                            match pattern with
                                | MatchValConModQualifier {modQualifier=(posModQual, _, {module_=(_, _, module_)})} ->
                                    match Map.tryFind (module_, name) dtenv with
                                        | Some ty -> ty
                                        | None ->
                                            printfn "%s%sError: Could not find value constructor declaration named %s in module named %s." (posString posModQual) (posString posn) module_ name
                                            failwith "Error"
                                | MatchValCon _ ->
                                    match Map.tryFind name tenv with
                                        | Some (_, ty) -> ty
                                        | None ->
                                            printfn "%sError: Could not find value constructor named %s." (posString posn) name
                                            failwith "Error"
                        let (valConPattern', index) =
                            match ty with
                                | FunTy {args=args; template=maybeFunTemplate; returnType=(_, _, funReturnType); source=Some {module_=srcModule; name=srcName}} ->
                                    let funReturnType' =
                                        match (maybeTemplate, maybeFunTemplate) with
                                            | (Some (_, _, template), Some (_, _, funTemplate)) ->
                                                let ty' = applyTemplateToFunctionType ty template
                                                let (FunTy {returnType=(_, _, returnType')}) = ty'
                                                returnType'
                                            | (None, None) ->
                                                funReturnType
                                            | (Some (posTemplate, _, _), None) ->
                                                printfn "%sType error: Value constructor does not have a template." (posString posTemplate)
                                                failwith "Type error"
                                            | (None, Some (posFunTemplate, _, _)) ->
                                                printfn "%sType error: Value constructor requires a template." (posString posn)
                                                failwith "Type error"
                                    if eqTypes funReturnType' pathTy then
                                        ()
                                    else
                                        printfn "%sType error: Value constructor given in pattern does not match the type of the expression." (posString posn)
                                    let unionDec = Map.find (unwrap srcModule, unwrap srcName) denv |> unwrap
                                    let index = match unionDec with
                                                    | UnionDec {valCons=valCons} ->
                                                        valCons |> unwrap |> List.tryFindIndex (fun (valConName, _) -> (unwrap valConName) = name)
                                                    | _ ->
                                                        printfn "%sType Error: Declaration named %s is not a value constructor." (posString posn) name
                                                        failwith "Type error"
                                    let index' =
                                        match index with
                                            | Some i -> i
                                            | None ->
                                                printfn "%sType Error: Declaration named %s is not a value constructor." (posString posn) name
                                                failwith "Type error"
                                    ((match List.tryHead args with
                                        | None ->
                                            dummyWrap MatchEmpty
                                        | Some h ->
                                            let path' = InternalValConAccess {valCon=(posn, None, path); typ=h}
                                            checkPattern' valConPattern path'), index')
                                | _ ->
                                    printfn "%sType Error: Declaration named %s is not a value constructor." (posString posn) name
                                    failwith "Type error"
                        match pattern with
                            | MatchValConModQualifier a ->
                                wrapWithType
                                    ty
                                    (MatchValConModQualifier {a with innerPattern = (posValConPattern, None, unwrap valConPattern');
                                                                     id = Some index})
                            | MatchValCon a ->
                                wrapWithType
                                    ty
                                    (MatchValCon {a with innerPattern = (posValConPattern, None, unwrap valConPattern');
                                                         id = Some index})
            pattern'
        (checkPattern' pattern path, tenv')

    match expr with
        | InlineCode (posc, _, code) ->
            wrapWithType
                (BaseTy (dummyWrap TyUnit))
                (InlineCode (posc, None, code))
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
        | SequenceExp (poss, _, exps) ->
            // This pattern match cannot fail since
            // sequences of length 0 are transformed to unit
            // expressions
            let (pose, _, exp)::rest = exps
            let (_, Some typee, cExp) = tc exp

            let tc' = match exp with
                          | LetExp {left=left; right=right} ->
                                let (_, tenv') = checkPattern (unwrap left) (unwrap right)
                                typeCheckExpr denv dtenv tenv' modNamesToTenvs capEnv
                          | _ -> tc

            let (seqType, cRest) =
                match rest with
                    // Last thing in the sequence
                    // so the type of the sequence is the type
                    // of the expression
                    | [] ->
                        (typee, [])
                    // Not the last thing in the sequence
                    // so the type of the sequence is the type
                    // of the rest
                    | _ ->
                        let (_, Some typer, SequenceExp (_, _, cRest)) = tc' (SequenceExp (dummyWrap rest))
                        (typer, cRest)
            (wrapWithType
                seqType
                (SequenceExp
                    (poss, Some seqType, (pose, Some typee, cExp)::cRest)
                ))
        // Hit a let expression that is not part of a sequence
        // In this case its variable bindings are useless, but the right hand side might still
        // produce side effects
        // We also have to make sure that the pattern matching agrees with the type of the right
        | LetExp { left=(posl, _, left); right=(posr, _, right) } ->
            let (_, Some typer, cRight) = tc right
            let (cPattern, _) = checkPattern left right
            wrapWithType
                typer
                (LetExp {
                    left=cPattern;
                    right=(posr, Some typer, cRight)
                })
        | VarExp {name=(posn, _, name)} ->
            let typ = match Map.tryFind name tenv with
                      | None ->
                            printfn "%sError: variable named %s could not be found." (posString posn) name
                            failwith "Error"
                      | Some (_, typ') -> typ'
            wrapWithType
                (typ)
                (VarExp {name=(posn, None, name)})
        | LambdaExp {clause=(posc, _, clause)} ->
            let args = unwrap clause.arguments |> List.map (fun (ty, name) -> (unwrap name, (false, unwrap ty)))
            let tenv' = tenv |> Map.map (fun name (mut, typ) -> (false, typ))
            let tenv'' = Map.merge tenv' (Map.ofList args)
            let tc' = typeCheckExpr denv dtenv tenv'' modNamesToTenvs capEnv
            let (posb, _, _) = clause.body
            let (posr, _, _) = clause.returnTy
            let (_, Some typeb, cBody) = tc' (unwrap clause.body)
            if eqTypes typeb (unwrap clause.returnTy) then
                ()
            else
                printfn "Type error in lambda expression: The return type %s in %s does not match the body type %s in %s." (unwrap clause.returnTy |> typeString) (posString posr) (typeString typeb) (posString posb)
                failwith "Type error"
            let argsTypes = unwrap clause.arguments |> List.unzip |> fst
            let lambdaType = FunTy {template=None;
                                    args=argsTypes;
                                    source=None;
                                    returnType=clause.returnTy}
            wrapWithType
                lambdaType
                (LambdaExp {clause=(posc, None, {
                    returnTy=clause.returnTy;
                    arguments=clause.arguments;
                    body=(posb, Some typeb, cBody)
                })})
        | AssignExp {left=(posl, _, left); right=(posr, _, right); ref=(posref, _, ref)} ->
            let (_, Some typer, cRight) = tc right
            let rec checkLeft left : TyExpr =
                match left with
                    | ModQualifierMutation {modQualifier=(_, _ , {module_=(_, _, module_); name=(_, _, name)})} ->
                        let typel = Map.find (module_, name) dtenv
                        match typel with
                            | RefTy _ -> typel
                            | _ -> printfn "%sError in set expression: The left side is not mutable." (posString posl)
                                   failwith "Error"
                    | VarMutation {varName=varName} ->
                        let (mutable_, typel) = Map.find (unwrap varName) tenv
                        if mutable_ || ref then
                            typel
                        else
                            printfn "%sError in set expression: The left hand side is not mutable." (posString posl)
                            failwith "Error"
                    | ArrayMutation {array=(posa, _, array); index=(posi, _, index)} ->
                        let (_, Some typei, cIndex) = tc index
                        if isIntType typei then
                            let tyArray = checkLeft array
                            match tyArray with
                                | ArrayTy {valueType=valueType} -> unwrap valueType
                                | ForallTy ty -> tyArray
                                | _ ->
                                    printfn "%sType error in array set expression: expected an array type for array access but was given %s instead." (posString posa) (typeString tyArray)
                                    failwith "Type error"
                        else
                            printfn "%sType error in array set expression: The index of the array has type %s, but was expected to have an integer type." (posString posi) (typeString typei)
                            failwith "Type error"
                    | RecordMutation {record=(posr, _, record); fieldName=(posf, _, fieldName)} ->
                        let tyRecord = checkLeft record
                        match tyRecord with
                            | (TyModuleQualifier qual | TyApply {tyConstructor=(_, _, TyModuleQualifier qual)}) ->
                                let actualDef = match Map.tryFind (toStringPair qual) denv with
                                                    | Some def -> unwrap def
                                                    | None -> printfn "%sType error: Cannot find declaration named %s in module %s." (posString posr) (unwrap qual.name) (unwrap qual.module_)
                                                              failwith "Type error"
                                let actualDef' = match tyRecord with
                                                     | TyModuleQualifier _ -> actualDef
                                                     | TyApply {args=args} -> applyTemplate actualDef (unwrap args)
                                                     | _ -> failwith "This should never happen"
                                match actualDef' with
                                    | RecordDec {fields=fields} ->
                                        let maybeFoundField = (List.tryFind (fun (ty, thisField) ->
                                                                                thisField = fieldName)
                                                                            (unwrap fields))
                                        match maybeFoundField with
                                            | None ->
                                                printfn "%sType error: could not find field named %s in record with type %s." (posString posf) fieldName (typeString tyRecord)
                                                failwith "Type error"
                                            | Some (ty, _) -> ty
                                    | _ ->
                                        printfn "%sType error: Can only access a record with the field lookup operation." (posString posr)
                                        failwith "Type error."
                            | ForallTy _ -> tyRecord
                            | _ -> printfn "%sType error: Attempted to access a field of a nonrecord with type %s." (posString posr) (typeString tyRecord)
                                   failwith "Type error"
            let typel = checkLeft left
            if ref then
                match typel with
                    | RefTy (posRefTy, _, refTy) ->
                        if eqTypes refTy typer then
                            ()
                        else
                            printfn "%sType error: The ref on the left hand side holds a value of type %s, which does not match the right hand side type of %s." (posString posl) (typeString refTy) (typeString typer)
                            failwith "Type error"
                    | ForallTy _ ->
                        ()
                    | _ ->
                        printfn "%sType error: The left hand side of the set expression has type %s, which is not a ref type." (posString posl) (typeString typel)
                        failwith "Type error"
            else
                if eqTypes typer typel then
                    ()
                else
                    printfn "%s%sType error: The left hand side of the set expression has type %s, but the right hand side has type %s. The left and the right hand sides were expected to have the same type." (posString posl) (posString posr) (typeString typel) (typeString typer)
                    failwith "Type error"
            wrapWithType
                typer
                (AssignExp {left=(posl, None, left); right=(posr, Some typer, cRight); ref=(posref, None, ref)})
        | RecordExp {recordTy=(posrt, _, recordTy); templateArgs=maybeTemplateArgs; initFields=(posif, _, initFields)} ->
            match recordTy with
                | ForallTy _ ->
                    wrapWithType
                        recordTy
                        (RecordExp {
                            recordTy = (posrt, None, recordTy);
                            templateArgs = maybeTemplateArgs
                            initFields = (posif, None, initFields)
                        })
                | TyModuleQualifier qual ->
                    let maybeActualDef = Map.tryFind (toStringPair qual) denv
                    match maybeActualDef with
                        | Some actualDef ->
                            match unwrap actualDef with
                                | RecordDec r0 ->
                                    let (r, resultType) =
                                        match maybeTemplateArgs with
                                            | None -> match r0.template with
                                                          | None -> (r0, recordTy)
                                                          | Some template ->
                                                              let tyVarArity = (unwrap template).tyVars |> unwrap |> List.length
                                                              printfn "%sType error: Record expression expects %d type arguments." (posString posrt) tyVarArity
                                                              failwith "Type error"
                                            | Some templateArgs ->
                                                let (RecordDec r1) = applyTemplate (RecordDec r0) (unwrap templateArgs)
                                                let newTy = TyApply {tyConstructor=(posrt, None, recordTy); args=templateArgs}
                                                (r1, newTy)
                                    // Now make sure that the field types are correct
                                    let flipTuple = fun (a,b) -> (b,a)    
                                    // Map of field names to what their types should be
                                    let defFieldsMap = Map.ofList (List.map flipTuple (unwrap r.fields))
                                    let initFieldNames = List.map fst initFields |> List.map unwrap
                                    let defFieldNames = unwrap r.fields |> List.map snd
                                    if List.hasDuplicates initFieldNames then
                                        printfn "%sType error: Duplicate field names in record expression." (posString posif)
                                        failwith "Type error"
                                    else
                                        ()
                                    let nameDiff = Set.difference (Set.ofList defFieldNames) (Set.ofList initFieldNames)
                                    if Set.isEmpty nameDiff then
                                        ()
                                    else
                                        let missingFields = String.concat "," nameDiff
                                        printfn "%sType error: Missing fields named %s from record expression." (posString posif) missingFields
                                        failwith "Type error"
                                    let cInitFields = (List.map (fun ((posfn, _, fieldName), (pose, _, expr)) ->
                                        let (_, Some typee, cExpr) = tc expr
                                        match Map.tryFind fieldName defFieldsMap with
                                            | None ->
                                                printfn "%sType error: Could not find field named %s in record of type %s." (posString posfn) fieldName (typeString recordTy)
                                                failwith "Type error"
                                            | Some fieldType ->
                                                if eqTypes typee fieldType then
                                                    ((posfn, None, fieldName), (pose, Some typee, cExpr))
                                                else
                                                    printfn "%sType error: Field named %s should have type %s but the expression given has type %s." (posString pose) fieldName (typeString fieldType) (typeString typee)
                                                    failwith "Type error"
                                        ) initFields)
                                    wrapWithType
                                        resultType
                                        (RecordExp {
                                            recordTy = (posrt, None, recordTy);
                                            templateArgs = maybeTemplateArgs;
                                            initFields = (posif, None, cInitFields)
                                        })
                                | _ -> printfn "%sType error: Could not find record type named %s in module named %s." (posString posrt) (unwrap qual.name) (unwrap qual.module_)
                                       failwith "Type error"
                        | None -> printfn "%sType error: Could not find record type named %s in module named %s." (posString posrt) (unwrap qual.name) (unwrap qual.module_)
                                  failwith "Type error"
                | _ -> printfn "%sType error: Attempting to access a record field of non-record type %s" (posString posrt) (typeString recordTy)
                       failwith "Type error"
        | ForLoopExp {typ=typ; varName=varName; start=(poss, _, start); direction=direction; end_=(pose, _, end_); body=(posb, _, body)} ->
            // First check that the starting exp is a numeral type
            let (_, Some types, cStart) = tc start
            if isIntType types then
                ()
            else
                printfn "%sType error: Starting expression has type of %s, which is not an integer type." (posString poss) (typeString types)
                failwith "Type error"
            // Now check that the starting exp is a numeral type
            let (_, Some typee, cEnd) = tc end_
            if isIntType typee then
                ()
            else
                printfn "%sType error: Ending expression has type of %s, which is not an integer type." (posString pose) (typeString typee)
                failwith "Type error"
            let tenv' = Map.add (unwrap varName) (false, unwrap typ) tenv
            let tc' = typeCheckExpr denv dtenv tenv' modNamesToTenvs capEnv
            let (_, Some typeb, cBody) = tc' body
            wrapWithType
                (BaseTy (dummyWrap TyUnit))
                (ForLoopExp {
                    typ=typ;
                    varName=varName;
                    start=(poss, Some types, cStart);
                    direction=direction;
                    end_=(pose, Some typee, cEnd);
                    body=(posb, Some typeb, cBody)
                })
        | DoWhileLoopExp {body=(posb, _, body); condition=(posc, _, condition)} ->
            let (_, Some typeb, _) = tc body
            let (_, Some typec, _) = tc condition
            if eqTypes typec (BaseTy (dummyWrap TyBool)) then
                ()
            else
                printfn "%sType error: Condition of do while loop expected to be of type bool but was of type %s." (posString posc) (typeString typec)
                failwith "Type error"
            wrapWithType
                (BaseTy (dummyWrap TyUnit))
                (DoWhileLoopExp {
                    body = (posb, Some typeb, body);
                    condition = (posc, Some typec, condition)
                })
        | WhileLoopExp {body=(posb, _, body); condition=(posc, _, condition)} ->
            let (_, Some typeb, cBody) = tc body
            let (_, Some typec, cCondition) = tc condition
            if eqTypes typec (BaseTy (dummyWrap TyBool)) then
                ()
            else
                printfn "%sType error: Condition of do while loop expected to be of type bool but was of type %s." (posString posc) (typeString typec)
                failwith "Type error"
            wrapWithType
                (BaseTy (dummyWrap TyUnit))
                (WhileLoopExp {
                    body = (posb, Some typeb, cBody);
                    condition = (posc, Some typec, cCondition)
                })
        | ArrayAccessExp {array=(posa, _, array); index=(posi, _, index)} ->
            let (_, Some typea, cArray) = tc array
            let (_, Some typei, cIndex) = tc index
            if isIntType typei then
                ()
            else
                printfn "%sType error: Array access index expression expected to have integer type, but was of type %s instead." (posString posi) (typeString typea)
                failwith "Type error"
            match typea with
                | ArrayTy {valueType=valueType} ->
                    wrapWithType
                        (unwrap valueType)
                        (ArrayAccessExp {
                            array=(posa, Some typea, cArray);
                            index=(posi, Some typei, index)
                        })
                | _ -> printfn "%sType error: Array access operation can only be applied to arrays, but was attempted to be applied to expression of type %s." (posString posa) (typeString typea)
                       failwith "Type error"
        | BinaryOpExp {left=(posl, _, left); op=(poso, _, op); right=(posr, _, right)} ->
            let (_, Some typel, cLeft) = tc left
            let (_, Some typer, cRight) = tc right
            match op with
                | (Add | Subtract | Multiply | Divide) ->
                    if isNumericalType typel then
                        ()
                    else
                        printfn "%sType error: The expression has a type of %s which is not a numerical type." (posString posl) (typeString typel)
                        failwith "Type error"
                    if isNumericalType typer then
                        ()
                    else
                        printfn "%sType error: The expression has a type of %s which is not a numerical type." (posString posr) (typeString typer)
                        failwith "Type error"
                    let numTypeResult = match (typel, typer) with
                                            | (BaseTy (_, _, t1), BaseTy (_, _, t2)) -> BaseTy (dummyWrap (arithResultTy t1 t2))
                                            | (ForallTy _, _) -> typel
                                            | (_, ForallTy _) -> typer
                                            | _ -> failwith "This should never happen"
                    wrapWithType
                        numTypeResult
                        (BinaryOpExp{
                            left=(posl, Some typel, cLeft)
                            right=(posr, Some typer, cRight)
                            op=(poso, None, op)
                        })
                | (GreaterOrEqual | LessOrEqual | Greater | Less) ->
                    if isNumericalType typel then
                        ()
                    else
                        printfn "%sType error: The expression has a type of %s which is not a numerical type." (posString posl) (typeString typel)
                    if isNumericalType typer then
                        ()
                    else
                        printfn "%sType error: The expression has a type of %s which is not a numerical type." (posString posr) (typeString typer)
                    wrapWithType
                        (BaseTy (dummyWrap TyBool))
                        (BinaryOpExp{
                            left=(posl, Some typel, cLeft)
                            right=(posr, Some typer, cRight)
                            op=(poso, None, op)
                        })
                | (LogicalOr | LogicalAnd) ->
                    match (typel, typer) with
                        | (BaseTy (_, _, TyBool), BaseTy (_, _, TyBool)) -> ()
                        | (BaseTy (_, _, TyBool), _) -> printfn "%sType error: Expected the expression to have type bool, but had type %s instead." (posString posr) (typeString typer)
                                                        failwith "Type error"
                        | _ -> printfn "%sType error: Expected the expression to have type bool, but had type %s instead." (posString posl) (typeString typel)
                               failwith "Type error"
                    wrapWithType
                        (BaseTy (dummyWrap TyBool))
                        (BinaryOpExp{
                            left=(posl, Some typel, cLeft)
                            right=(posr, Some typer, cRight)
                            op=(poso, None, op)
                        })
                | (Equal | NotEqual) ->
                    if eqTypes typel typer then
                        wrapWithType
                            (BaseTy (dummyWrap TyBool))
                            (BinaryOpExp{
                                left=(posl, Some typel, cLeft)
                                right=(posr, Some typer, cRight)
                                op=(poso, None, op)
                            })   
                    else
                        printfn "%s%sType error: Expected the left and right hand side to have the same types, but the left hand side is of type %s while the right hand side is of type %s" (posString posl) (posString posr) (typeString typel) (typeString typer)
                        failwith "Type error"
                | (Modulo | BitwiseAnd | BitwiseOr) ->
                    if isIntType typel then
                        ()
                    else
                        printfn "%sType error: Expected an expression of integer type but the type of the expression is %s instead." (posString posl) (typeString typel)
                        failwith "Type error"
                    if isIntType typer then
                        ()
                    else
                        printfn "%sType error: Expected an expression of integer type but the type of the expression is %s instead." (posString posr) (typeString typer)
                        failwith "Type error"
                    let numTypel = match typel with
                                       | BaseTy (_, _, t1) -> t1
                                       | _ -> failwith "This should never happen"
                    let numTyper = match typer with
                                       | BaseTy (_, _, t1) -> t1
                                       | _ -> failwith "This should never happen"
                    let numTypeResult = arithResultTy numTypel numTyper
                    wrapWithType
                        (BaseTy (dummyWrap numTypeResult))
                        (BinaryOpExp{
                            left=(posl, Some typel, cLeft)
                            right=(posr, Some typer, cRight)
                            op=(poso, None, op)
                        })
        | ArrayLitExp (pose, _, []) ->
            printfn "%sSemantic error: Array literals of length zero are not allowed." (posString pose)
            failwith "Semantic error"
        | ArrayLitExp (pose, _, exps) ->
            let (_, _, head)::_ = exps
            let (_, Some typeh, _) = tc head
            let expsTys = (List.map (fun (posexp, _, exp) ->
                let (_, Some typeexp, cExp) = tc exp
                if eqTypes typeexp typeh then
                    (posexp, Some typeexp, cExp)
                else
                    printfn "%sType error: Expression in array literal expected to have type %s but has type %s instead." (posString posexp) (typeString typeh) (typeString typeexp)
                    failwith "Type error"
            ) exps)
            let capacity = sprintf "%d" (List.length exps) |> dummyWrap |> CapacityConst
            (wrapWithType
                (ArrayTy {valueType=dummyWrap typeh; capacity=dummyWrap capacity})
                (ArrayLitExp (pose, None, expsTys)))
        | CallExp {func=(posf, _, func); args=(posa, _, args)} ->
            let (_, Some typef, cFunc) = tc func
            let tcArgs = args |> List.map (unwrap >> tc)
            match typef with
                | FunTy {template=None; args=funArgs; returnType=returnType} ->
                    if List.length tcArgs = List.length funArgs then
                        List.iter (fun ((posArg, _, _), (_, Some typea, tcArg), (_, _, fArg)) ->
                            if eqTypes typea fArg then
                                ()
                            else
                                printfn "%sType error: Function argument expected to be of type %s but was of type %s." (posString posArg) (typeString fArg) (typeString typea)
                                failwith "Type error"
                        ) (List.zip3 args tcArgs funArgs)
                        wrapWithType
                            (unwrap returnType)
                            (CallExp {
                                func=(posf, Some typef, cFunc)
                                args=(posa, None, tcArgs)
                            })
                    else
                        printfn "%sType error: incorrect number of arguments applied to function of type %s." (posString posa) (typeString typef)
                        failwith "Type error"
                | FunTy {template=Some _} ->
                    printfn "%sType error: Expected type arguments to be applied before calling function. The type of the function being called is %s." (posString posf) (typeString typef)
                    failwith "Type error"
        | UnaryOpExp {op=(poso, _, op); exp=(pose, _, exp)} ->
            let (_, Some typee, cExp) = tc exp
            match op with
                | LogicalNot ->
                    if eqTypes typee (BaseTy (dummyWrap TyBool)) then
                        wrapWithType
                            (BaseTy (dummyWrap TyBool))
                            (UnaryOpExp {
                                op=(poso, None, op);
                                exp=(pose, Some typee, cExp)
                            })
                    else
                        printfn "%sType error: Expression has type %s when type bool was expected for logical not expression." (posString pose) (typeString typee)
                        failwith "Type error"
                | BitwiseNot ->
                    if isIntType typee then
                        wrapWithType
                            typee
                            (UnaryOpExp {
                                op=(poso, None, op);
                                exp=(pose, Some typee, cExp)
                            })
                    else
                        printfn "%sType error: Expression has type %s when integer type was expected for bitwise not operation." (posString pose) (typeString typee)
                        failwith "Type error"
        | RecordAccessExp {record=(posr, _, record); fieldName=(posf, _, fieldName)} ->
            let (_, Some typer, cRecord) = tc record
            match typer with
                | ForallTy _ ->
                    wrapWithType
                        typer
                        (RecordAccessExp {
                            record=(posr, Some typer, cRecord);
                            fieldName=(posf, None, fieldName)
                        })
                | (TyModuleQualifier qual | TyApply {tyConstructor=(_, _, TyModuleQualifier qual)}) ->
                    let actualDef = unwrap (Map.find (toStringPair qual) denv)
                    let actualDef' = match typer with
                                         | TyModuleQualifier _ -> actualDef
                                         | TyApply {args=args} -> applyTemplate actualDef (unwrap args)
                                         | _ -> failwith "This should never happen"
                    match actualDef' with
                        | RecordDec {fields=fields} ->
                            match List.tryFind (snd >> (=) fieldName) (unwrap fields) with
                                | Some (ty, _) ->
                                    // Found the field. Everything is good.
                                    wrapWithType
                                        ty
                                        (RecordAccessExp {
                                            record = (posr, Some typer, cRecord)
                                            fieldName = (posf, None, fieldName)
                                        })
                                | None ->
                                    printfn "%sType error: Field named %s not found in record of type %s." (posString posf) fieldName (typeString typer)
                                    failwith "Type error"
                        | _ ->
                            printfn "%sType error: Trying to access field of a nonrecord type." (posString posr)
                            failwith "Type error"
                | _ ->
                    printfn "%sType error: Trying to access field of a nonrecord type %s." (posString posr) (typeString typer)
                    failwith "Type error"
        | ModQualifierExp {module_=(posm, _, module_); name=(posn, _, name)} ->
            let ty = match Map.tryFind (module_, name) dtenv with
                         | Some ty -> ty
                         | None -> printfn "%s%sError: Could not find declaration named %s in module named %s." (posString posm) (posString posn) name module_
                                   failwith "Error"
            wrapWithType
                ty
                (ModQualifierExp {module_=(posm, None, module_); name=(posn, None, name)})
        | TemplateApplyExp {func=(posf, _, func); templateArgs=(posTempArgs, _, templateArgs)} ->
            let (_, Some typef, cFunc) = tc func
            match typef with
                | FunTy {template=None} ->
                    printfn "%sType error: Function does not require application of a template." (posString posf)
                    failwith "Type error"
                | FunTy {template=Some _} ->
                    match func with
                        | (VarExp _ | ModQualifierExp _) -> ()
                        | _ -> printfn "%sSemantic error: Template can only be applied directly to a function." (posString posf)
                               failwith "Semantic error"
                    match typef with
                        | FunTy {source=Some {module_=(_, _, module_); name=(_, _, name)}} ->
                            let funDec = Map.find (module_, name) denv |> unwrap
                            if isAlreadyCheckedFunction {module_=dummyWrap module_; name=dummyWrap name} templateArgs then
                                ()
                            else
                                let tenvOfFunc = Map.find module_ modNamesToTenvs
                                addToAlreadyCheckedFunctions {module_=dummyWrap module_; name=dummyWrap name} templateArgs
                                applyTemplate funDec templateArgs |> typecheckDec denv dtenv tenvOfFunc modNamesToTenvs |> ignore
                        | _ -> ()
                    wrapWithType
                        (applyTemplateToFunctionType typef templateArgs)
                        (TemplateApplyExp {func=(posf, Some  typef, cFunc); templateArgs=(posTempArgs, None, templateArgs)})
                | _ ->
                    printfn "%sType error: Attempting to apply a template to an expression of type %s. Templates can only be applied to functions." (posString posf) (typeString typef)
                    failwith "Type error"
        | RefExp (pose, _, expr) ->
            let (_, Some typee, cExpr) = tc expr
            wrapWithType
                (RefTy (pose, None, typee))
                (RefExp (pose, Some typee, cExpr))
        | TupleExp tuple ->
            let (typeCheckedTuple, tupleTypes) = (List.map (fun (pose, _, expr) ->
                                                    let (_, Some typee, cExpr) = tc expr
                                                    ((pose, Some typee, cExpr),
                                                     (pose, None, typee))
                                                  ) tuple) |> List.unzip
            wrapWithType
                (TupleTy tupleTypes)
                (TupleExp typeCheckedTuple)
        | CaseExp {on=(posOn, _, on); clauses=(posClauses, _, clauses)} ->
            let (_, Some typeOn, cOn) = tc on
            let clauses' = clauses |> List.map (fun ((posOverallPattern, _, overallPattern), (posExprIfMatched, _, exprIfMatched)) ->
                        let ((_, typeOverallPattern, cOverallPattern), tenv') = checkPattern overallPattern on
                        let (_, Some typeExprIfMatched, cExprIfMatched) = typeCheckExpr denv dtenv tenv' modNamesToTenvs capEnv exprIfMatched
                        ((posOverallPattern, typeOverallPattern, cOverallPattern),
                         (posExprIfMatched, Some typeExprIfMatched, cExprIfMatched)))
            let (_, (_, Some resultTy, _)) = List.head clauses'
            // All bodies in the case expression must return the same type
            clauses' |> List.iter (fun (_, (posExprIfMatched, Some typeExprIfMatched, _)) ->
                                        if eqTypes typeExprIfMatched resultTy then
                                            ()
                                        else
                                            printfn "%sType error: Expected all bodies of case expression to have type %s, but this body had type %s instead." (posString posExprIfMatched) (typeString resultTy) (typeString typeExprIfMatched)
                                            failwith "Type error")
            wrapWithType
                resultTy
                (CaseExp {
                    on=(posOn, Some typeOn, cOn);
                    clauses=(posClauses, None, clauses')})
        | DerefExp (pose, _, expr) ->
            let (_, Some typee, cExpr) = tc expr
            let returnTy = match typee with
                               | RefTy (_, _, ty) -> ty
                               | _ -> printfn "%sType error: Attempting to dereference a non-reference expression of type %s" (posString pose) (typeString typee)
                                      failwith "Type error"
            wrapWithType
                returnTy
                (DerefExp (pose, Some typee, cExpr))
        | ArrayMakeExp { typ=(post, _, typ); initializer=(posi, _, initializer) } ->
            match typ with
                | ArrayTy _ -> ()
                | _ -> printfn "%sType error: Expected an array type in array initializer expression." (posString post)
                       failwith "Type error"
            let (_, Some typei, cInitializer) = tc initializer
            wrapWithType
                typ
                (ArrayMakeExp { typ=(post, None, typ); initializer=(posi, Some typei, cInitializer) })
        | InternalValConAccess { valCon=valCon; typ=typ } ->
            wrapWithType
                (unwrap typ)
                (InternalValConAccess { valCon=valCon; typ=typ })
        | UnitExp (posu, _, ()) ->
            wrapWithType
                (BaseTy (dummyWrap TyUnit))
                (UnitExp (posu, None, ()))
        | FloatExp (posf, _, number) ->
            wrapWithType
                (BaseTy (dummyWrap TyFloat))
                (FloatExp (posf, None, number))
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

and typecheckDec denv dtenv tenv modNamesToTenvs dec =
    match dec with
        | LetDec {varName=varName; typ=(postyp, _, typ); right=(posr, _, right)} ->
            let (_, Some typeRhs, cRight) = typeCheckExpr denv dtenv tenv modNamesToTenvs Set.empty right
            if eqTypes typ typeRhs then
                LetDec {varName=varName;
                        typ=(postyp, None, typ);
                        right=(posr, Some typeRhs, cRight)}
            else
                printfn "%s%sType error: The let declaration's left hand side type of %s did not match the right hand side type of %s" (posString postyp) (posString posr) (typeString typ) (typeString typeRhs)
                failwith "Type error"
        | FunctionDec {name=name; template=template; clause=(posc, _, clause)} ->
            let (posargs, _, arguments) = clause.arguments
            let (posbody, _, body) = clause.body
            let (posret, _, return_) = clause.returnTy
            let argTenv = arguments |> List.map (fun (argTy, argName) -> (unwrap argName, (false, unwrap argTy))) |> Map.ofList
            let tenv' = Map.merge tenv argTenv
            // Capacity variables are also available inside the function!
            let tenv'' = match template with
                             | Some (_, _, temp) ->
                                 let capType = BaseTy (dummyWrap TyInt32)
                                 let capTenv = temp.capVars |> unwrap |> List.map (unwrap >> fun capName -> (capName, (false, capType))) |> Map.ofList
                                 Map.merge capTenv tenv'
                             | None -> tenv'
            let capEnv = match template with
                             | Some (_, _, temp) ->
                                 temp.capVars |> unwrap |> List.map unwrap |> Set.ofList
                             | None -> Set.empty
            
            // Check that all capacity variable references are valid
            TreeTraversals.map1 (fun (cap : CapacityExpr) ->
                match cap with
                    | CapacityNameExpr (posn, _, name) ->
                        if Set.contains name capEnv then
                            cap
                        else
                            printfn "%sError: capacity variable named %s does not exist." (posString posn) name
                            failwith "Error"
                    | _ -> cap
            ) clause |> ignore

            let (_, Some bodyTy, cBody) = typeCheckExpr denv dtenv tenv'' modNamesToTenvs capEnv body
            // Check that the type of the body matches the given return type
            if eqTypes bodyTy return_ then
                FunctionDec{
                    name=name;
                    template=template;
                    clause=(posc, None, {
                        returnTy=(posret, None, return_);
                        arguments=(posargs, None, arguments);
                        body=(posbody, Some bodyTy, cBody)
                    })
                }
            else
                printfn "%s%sType error: The body of the function returns a value of type %s, but the function was declared to return type %s." (posString posret) (posString posbody) (typeString bodyTy) (typeString return_)
                failwith "Type error"
        | RecordDec {name=name; fields=(posf, _, fields); template=maybeTemplate} ->
            if fields |> List.map snd |> List.hasDuplicates then
                printfn "%sSemantic error: The record declaration contains duplicate field names." (posString posf)
                failwith "Semantic error"
            else
                // Check that the record's template variables are valid
                match maybeTemplate with
                    | None -> ()
                    | Some (posTemp, _, template) ->
                        let allowedTyVars = template.tyVars |> unwrap |> List.map unwrap |> Set.ofList
                        let validateTyVar ty =
                            match ty with
                                | ForallTy (posname, _, name) ->
                                    if Set.contains name allowedTyVars then
                                        ()
                                    else
                                        printfn "%sType error: Unknown type %s" (posString posname) (typeString ty)
                                        failwith "Type error"
                                | _ -> ()
                        fields |> List.map fst |> List.iter validateTyVar
                RecordDec {name=name; fields=(posf, None, fields); template=maybeTemplate}
        | x -> x

// Finally we can typecheck each module!
let typecheckModule (Module decs0) denv dtenv menv tenv modNamesToTenvs : Module =
    let typeCheckExpr' = typeCheckExpr denv dtenv tenv
    // TRANSFORM: Begin by transforming all type names to the
    // more accurate module qualifier (ie, the absolute path to the type)
    let decs = (TreeTraversals.map1 (fun (tyExpr : TyExpr) ->
        match tyExpr with
            | TyName (pos, _, name) ->
                if Map.containsKey name menv then
                    TyModuleQualifier (toModuleQual (Map.find name menv))
                else
                    printfn "Type error in %s: the type %s does not exist." (posString pos) name
                    failwith "Type error"
            | x -> x
    ) decs0)
    Module (List.map (fun (pos, _, dec) ->
        (pos, None, typecheckDec denv dtenv tenv modNamesToTenvs dec)
    ) decs)

let typecheckProgram (modlist0 : Module list) (fnames : string list) : Module list =
    // TRANSFORM: Transform empty sequences to a unit expression
    let modlist1 = (TreeTraversals.map1 (fun expr ->
        match expr with
            | SequenceExp (pos, ty, []) -> UnitExp (pos, ty, ())
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
            if List.hasDuplicates tyVars' then
                printfn "Semantic error in %s: Template contains duplicate definitions of a type parameter" (posString tpos)
                failwith "Semantic error"
            elif List.hasDuplicates capVars' then
                printfn "Semantic error in %s: Template contains duplicate definitions of a capacity parameter" (posString cpos)
                failwith "Semantic error"
            else
                ()
        (List.iter (fun (_, _, dec) ->
            match dec with
                | FunctionDec {template=Some template} -> checkTemplate (unwrap template)
                | UnionDec {template=Some template} -> checkTemplate (unwrap template)
                | RecordDec {template=Some template} -> checkTemplate (unwrap template)
                | _ -> ()
        ) decs)
    ) (List.zip modlist1 fnames))

    // SEMANTIC CHECK: Declarations in the module have unique names
    (List.iter (fun (Module decs) ->
        let _ = (List.fold (fun names dec ->
            if isNamedDec (unwrap dec) then
                let (posn, _, name) = nameOfDec (unwrap dec)
                if Set.contains name names then
                    printfn "%sSemantic error: Module already contains duplicate declarations named %s." (posString posn) name
                    failwith "Semantic error"
                else
                    (Set.add name names) : Set<string>
            else
                names
        ) Set.empty decs)
        ()
    ) modlist1)

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
                Map.add name2 (unwrap modName, unwrap name) map2
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
                Map.merge (Map.find nameToMerge modNamesToExportedMenvs) menv1 
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
                                TyModuleQualifier (toModuleQual (Map.find name menv))
                            else
                                printfn "Type error in %s: the type %s does not exist." (posString pos) name
                                failwith "Type error"
                        | x -> x
                ) module_))
            modlist1


    // Maps module qualifiers to their actual declarations
    let denv = (List.fold (fun map (Module decs) ->
        let modName = nameInModule (Module decs)
        let namedDecs = List.filter (unwrap >> isNamedDec) decs
        List.fold (fun map2 dec0 ->
            let decName = nameOfDec (unwrap dec0)
            let qual = (unwrap modName, unwrap decName)
            Map.add qual dec0 map2) map namedDecs
    ) Map.empty modlist2)

    // Maps module qualifiers to their types
    let dtenv = (List.fold (fun map0 (Module decs) ->
        let modName = nameInModule (Module decs)
        (List.fold (fun map1 dec ->
            match unwrap dec with
                | LetDec {typ=typ; varName=varName} ->
                    Map.add (unwrap modName, unwrap varName) (unwrap typ) map1
                | FunctionDec {name=name; clause=(_, _, clause); template=template} ->
                    let args = clause.arguments |> unwrap |> List.unzip |> fst
                    let ty = FunTy {template=template;
                                    source=Some {module_=modName; name=name}
                                    returnType=clause.returnTy;
                                    args=args}
                    Map.add (unwrap modName, unwrap name) ty map1
                | UnionDec union_ ->
                    let returnType = TyModuleQualifier {module_=modName; name=union_.name}
                    let returnType' =
                        match union_.template with
                            | None -> returnType
                            | Some (_, _, template) ->
                                // Convert the Template type to a TemplateApply type
                                TyApply {tyConstructor=dummyWrap returnType; args=dummyWrap (templateToTemplateApply template)}
                    // Add all of the value constructors as functions
                    (List.fold (fun map1 (conName, typ) ->
                        let args = match typ with
                                       | None -> []
                                       | Some x -> [x]
                        Map.add (unwrap modName, unwrap union_.name) (FunTy {template=union_.template;
                                                                             source=Some {module_=modName; name=union_.name};
                                                                             returnType=dummyWrap returnType';
                                                                             args=args}) map1
                    ) map0 (unwrap union_.valCons))
                | _ -> map0
          ) map0 decs)
    ) Map.empty modlist2)

    // Maps module names to type environments
    // Each type environment maps variable names to type expressions
    let modNamesToTenvs =
        // Now build the type environments for every module
        // maps names to module qualifiers
        let tenvs0 = (List.map (fun (Module decs) ->
            let modName = nameInModule (Module decs)
            List.fold (fun map0 dec ->
                match unwrap dec with
                    | LetDec let_ ->
                        Map.add (unwrap let_.varName) (false, (unwrap let_.typ)) map0
                    | FunctionDec fun_ ->
                        let clause = unwrap fun_.clause
                        let args = clause.arguments |> unwrap |> List.unzip |> fst
                        Map.add (unwrap fun_.name) (false, FunTy {template=fun_.template;
                                                                  source=Some {module_=modName; name=fun_.name}
                                                                  returnType=clause.returnTy;
                                                                  args=args}) map0
                    // Type unions add their value constructors as functions
                    // to the type environment
                    | UnionDec union_ ->
                        let returnType = TyModuleQualifier {module_=modName; name=union_.name}
                        let returnType' =
                            match union_.template with
                                | None -> returnType
                                | Some (_, _, template) ->
                                    // Convert the Template type to a TemplateApply type
                                    let tyExprs = template.tyVars |> unwrap |> List.map (ForallTy >> dummyWrap) |> dummyWrap
                                    let capExprs = template.capVars |> unwrap |> List.map (CapacityNameExpr >> dummyWrap) |> dummyWrap
                                    TyApply {tyConstructor=dummyWrap returnType; args=dummyWrap {tyExprs=tyExprs; capExprs=capExprs}}
                        // Add all of the value constructors as functions
                        List.fold (fun map1 (conName, typ) ->
                            let args = match typ with
                                           | None -> []
                                           | Some x -> [x]
                            Map.add (unwrap conName) (false, FunTy {template=union_.template;
                                                                    source=Some {module_=modName; name=union_.name};
                                                                    returnType=dummyWrap returnType';
                                                                    args=args}) map1
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
                Map.merge (Map.find nameToMerge modNamesToExportedTenvs) tenv1 
            ) tenv0 allOpens
        ) modNamesToTenvs0)
    
    (List.map (fun module_ ->
        let moduleName = unwrap (nameInModule module_)
        typecheckModule module_ denv dtenv (Map.find moduleName modNamesToMenvs) (Map.find moduleName modNamesToTenvs) modNamesToTenvs
    ) modlist2)