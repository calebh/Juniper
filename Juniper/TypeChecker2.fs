module TypeChecker2
module A = Ast2
module T = TypedAst
open Constraint
open FParsec
open System.IO
open Extensions
open QuickGraph.Algorithms

exception TypeError of string
exception SemanticError of string

let baseTy b = T.TyCon <| T.BaseTy b
let unittype = baseTy T.TyUnit
let booltype = baseTy T.TyBool
let int8type = baseTy T.TyInt8
let uint8type = baseTy T.TyUint8
let int16type = baseTy T.TyInt16
let uint16type = baseTy T.TyUint16
let int32type = baseTy T.TyInt32
let uint32type = baseTy T.TyUint32
let int64type = baseTy T.TyInt64
let uint64type = baseTy T.TyUint64
let floattype = baseTy T.TyFloat
let doubletype = baseTy T.TyDouble
let pointertype = baseTy T.TyPointer

let flip f a b = f b a

// Get position of the error (starting line and column, end line and column) in the form of a string to be used
// for error messages.
let posString (p1 : Position, p2' : Position) : string =
    let p2 =
        if p1 = p2' then
            // The error should span at least one character
            new Position(p2'.StreamName, p2'.Index, p2'.Line, p2'.Column + 1L)
        else
            p2'
    let p1l = p1.Line - 1L
    let p2l = p2.Line - 1L
    let p1c = p1.Column - 1L
    let p2c = p2.Column - 1L
    let inRange line column =
        let notInRange = line < p1l ||
                         line > p2l ||
                         (line = p1l && column < p1c) ||
                         (line = p2l && column >= p2c)
        not notInRange
    let badCode =
        if File.Exists p1.StreamName then
            let lines = File.ReadAllLines p1.StreamName
            let relevantLines = lines.[int(p1l) .. int(p2l)]
            let arrows = Array.create relevantLines.Length (Array.create 0 ' ')
            for line in p1l .. p2l do
                let line' = line - p1l
                let lineLength = relevantLines.[int(line')].Length
                let arrowLine = Array.create lineLength ' '
                Array.set arrows (int(line')) arrowLine
                for column in 0 .. lineLength - 1 do
                    if inRange line (int64(column)) then
                        Array.set arrowLine column '^'
            let flattenedArrows = List.ofArray arrows |> List.map System.String.Concat
            let final = List.zip (List.ofArray relevantLines) flattenedArrows |> List.map (fun (a,b) -> a+"\n"+b+"\n") |> System.String.Concat
            sprintf "\n\n%s\n" final
        else
            ""
    sprintf "file %s, line %d column %d to line %d column %d%s" p1.StreamName (p1l + 1L) p1c (p2l + 1L) p2c badCode

let errStr pos err = lazy(sprintf "%s\n\n%s" (List.map posString pos |> String.concat "\n\n") err)

let decRefs valueDecs (menv : Map<string, string*string>) localVars e =
    let rec getVars pattern =
        match pattern with
        | (A.MatchFalse _ | A.MatchFloatVal _ | A.MatchIntVal _ | A.MatchTrue _ |
            A.MatchUnderscore _ | A.MatchUnit _) ->
            Set.empty
        | A.MatchRecCon {fields=(_, fields)} ->
            Set.unionMany (List.map (snd >> A.unwrap >> getVars) fields)
        | A.MatchTuple (_, elements) ->
            Set.unionMany (List.map (A.unwrap >> getVars) elements)
        | A.MatchValCon {name=(_, name); innerPattern=innerPattern} ->
            innerPattern |> Option.map (A.unwrap >> getVars) |> Option.toList |> Set.unionMany
        | A.MatchVar {varName=(_, varName)} ->
            Set.singleton varName

    let rec dl localVars l =
        let dl' = dl localVars
        match l with
        | A.ArrayMutation {array=(_, array); index=(_, index)} ->
            Set.union (dl' array) (d localVars index)
        | A.ModQualifierMutation (_, {module_=(_, module_); name=(_, name)}) ->
            let modqual = (module_, name)
            if Set.contains modqual valueDecs then
                Set.singleton modqual
            else
                Set.empty
        | A.RecordMutation {record=(_, record)} ->
            dl' record
        | A.VarMutation (_, name) ->
            match Map.tryFind name menv with
            | Some modqual when Set.contains modqual valueDecs ->
                Set.singleton modqual
            | _ -> Set.empty

    and d localVars e =
        let d' = d localVars
        match e with
        | A.ArrayAccessExp {array=(_, array); index=(_, index)} ->
            Set.union (d' array) (d' index)
        | A.ArrayLitExp (_, exprs) ->
            Set.unionMany (List.map (A.unwrap >> d') exprs)
        | A.ArrayMakeExp {initializer=Some (_, initializer)} ->
            d' initializer
        | A.ArrayMakeExp _ ->
            Set.empty
        | A.AssignExp {left=(_, left); right=(_, right)} ->
            Set.union (dl localVars left) (d' right)
        | A.BinaryOpExp {left=(_, left); right=(_, right)} ->
            Set.union (d' left) (d' right)
        | A.CallExp {func=(_, func); args=(_, args)} ->
            Set.unionMany ((d' func)::(List.map (A.unwrap >> d') args))
        | A.CaseExp {on=(_, on); clauses=(_, clauses)} ->
            let s1 = d' on
            let s2 =
                clauses |>
                List.map
                    (fun ((_, pat), (_, expr)) ->
                        let localVars' = Set.union (getVars pat) localVars
                        d localVars' expr)
            Set.unionMany (s1::s2)
        | A.DerefExp (_, expr) ->
            d' expr
        | A.DoWhileLoopExp {condition=(_, condition); body=(_, body)} ->
            Set.union (d' condition) (d' body)
        | A.FalseExp _ ->
            Set.empty
        | A.FloatExp _ ->
            Set.empty
        | A.DoubleExp _ ->
            Set.empty
        | A.ForLoopExp {varName=(_, varName); start=(_, start); end_=(_, end_); body=(_, body)} ->
            let s1 = d' start
            let s2 = d' end_
            let s3 = d (Set.add varName localVars) body
            Set.unionMany [s1; s2; s3]
        | A.IfElseExp {condition=(_, condition); trueBranch=(_, trueBranch); falseBranch=(_, falseBranch)} ->
            [condition; trueBranch; falseBranch] |> List.map d' |> Set.unionMany
        | A.InlineCode _ ->
            Set.empty
        | (A.IntExp _ | A.Int8Exp _ | A.UInt8Exp _ | A.Int16Exp _ | A.UInt16Exp _ |
            A.UInt32Exp _ | A.Int32Exp _ | A.UInt64Exp _ | A.Int64Exp _) ->
            Set.empty
        | A.LambdaExp (_, {arguments=(_, arguments); body=(_, body)}) ->
            let argNames = arguments |> List.map (fst >> A.unwrap) |> Set.ofList
            d (Set.union argNames localVars) body
        | A.LetExp {right=(_, right)} ->
            d' right
        | A.ModQualifierExp (_, {module_=(_, module_); name=(_, name)}) ->
            let modqual = (module_, name)
            if Set.contains modqual valueDecs then
                Set.singleton modqual
            else
                Set.empty
        | A.NullExp _ ->
            Set.empty
        | A.QuitExp _ ->
            Set.empty
        | A.RecordAccessExp {record=(_, record)} ->
            d' record
        | A.RecordExp {initFields=(_, initFields)} ->
            initFields |> List.map (snd >> A.unwrap >> d') |> Set.unionMany
        | A.RefExp (_, expr) ->
            d' expr
        | A.SequenceExp (pose, exprs) ->
            let (pos, exp)::rest = exprs
            let localVars' =
                Set.union
                    localVars
                    (match exp with
                    | A.LetExp {left=(_, left)} ->
                        getVars left
                    | _ ->
                        Set.empty)
            let s1 = d' exp
            let s2 =
                if List.isEmpty rest then
                    Set.empty
                else
                    d localVars' (A.SequenceExp (pose, rest))
            Set.union s1 s2
        | A.TemplateApplyExp {func=(posf, func)} ->
            match func with
            | Choice1Of2 name ->
                if Set.contains name localVars then
                    Set.empty
                else
                    match Map.tryFind name menv with
                    | Some modqual when Set.contains modqual valueDecs ->
                        Set.singleton modqual
                    | _ ->
                        Set.empty
            | Choice2Of2 {module_=(_, module_); name=(_, name)} ->
                let modqual = (module_, name)
                if Set.contains modqual valueDecs then
                    Set.singleton modqual
                else
                    Set.empty
        | A.TrueExp _ ->
            Set.empty
        | A.TupleExp exprs ->
            exprs |> List.map (A.unwrap >> d') |> Set.unionMany
        | A.TypeConstraint {exp=(_, exp)} ->
            d' exp
        | A.UnaryOpExp {exp=(_, exp)} ->
            d' exp
        | A.UnitExp _ ->
            Set.empty
        | A.UnsafeTypeCast {exp=(_, exp)} ->
            d' exp
        | A.VarExp (posv, varName) ->
            if Set.contains varName localVars then
                Set.empty
            else
                match Map.tryFind varName menv with
                | Some modqual when Set.contains modqual valueDecs ->
                    Set.singleton modqual
                | _ ->
                    Set.empty
        | A.WhileLoopExp {condition=(_, condition); body=(_, body)} ->
            Set.union (d' condition) (d' body)
    d localVars e

let convertTemplate ({tyVars=(_, tyVars); capVars=maybeCapVars} : A.Template) =
    let t = List.map A.unwrap tyVars
    let c = Option.map A.unwrap maybeCapVars |> Option.toList |> List.concat |> List.map A.unwrap
    ({tyVars=t; capVars=c} : T.Template)

// The mapping parameter is used to convert explicitly given type variable parameter
// into a non-conflicting form
let rec convertType menv tyVarMapping capVarMapping (tau : A.TyExpr) : T.TyExpr =
    let ct = convertType menv tyVarMapping capVarMapping
    let convertCapacity = convertCapacity capVarMapping
    match tau with
    | A.ApplyTy {tyConstructor=(_, tyConstructor); args=(_, {tyExprs=(_, tyExprs); capExprs=(_, capExprs)})} ->
        T.ConApp (ct tyConstructor, List.map (A.unwrap >> ct) tyExprs, List.map (A.unwrap >> convertCapacity) capExprs)
    | A.ArrayTy {valueType=(_, valueType); capacity=(_, capacity)} ->
        T.ConApp (T.TyCon T.ArrayTy, [ct valueType], [convertCapacity capacity])
    | A.BaseTy (_, tau) ->
        T.TyCon <| T.BaseTy (match tau with
                                | A.TyUint8 -> T.TyUint8
                                | A.TyUint16 -> T.TyUint16
                                | A.TyUint32 -> T.TyUint32
                                | A.TyUint64 -> T.TyUint64
                                | A.TyInt8 -> T.TyInt8
                                | A.TyInt16 -> T.TyInt16
                                | A.TyInt32 -> T.TyInt32
                                | A.TyInt64 -> T.TyInt64
                                | A.TyBool -> T.TyBool
                                | A.TyDouble -> T.TyDouble
                                | A.TyFloat -> T.TyFloat
                                | A.TyPointer -> T.TyPointer
                                | A.TyUnit -> T.TyUnit)
    | A.FunTy {template=maybeTemplate; args=args; returnType=(_, returnType)} ->
        let returnType' = ct returnType
        let args' = List.map A.unwrap args
        T.ConApp (T.TyCon T.FunTy, returnType'::(List.map (A.unwrap >> ct) args), [])
    | A.ModuleQualifierTy {module_=(_, module_); name=(_, name)} ->
        T.TyCon <| T.ModuleQualifierTy {module_=module_; name=name}
    | A.NameTy (_, name) ->
        let (module_, name) = Map.find name menv
        T.TyCon <| T.ModuleQualifierTy {module_=module_; name=name}
    | A.ParensTy (_, tau) ->
        ct tau
    | A.RefTy (_, tau) ->
        T.ConApp (T.TyCon T.RefTy, [ct tau], [])
    | A.TupleTy taus ->
        T.ConApp (T.TyCon T.TupleTy, List.map (A.unwrap >> ct) taus, [])
    | A.VarTy (_, name) ->
        Map.findDefault name (T.TyVar name) tyVarMapping

and convertCapacity capVarMapping (cap : A.CapacityExpr) : T.CapacityExpr =
    let convertCapacity = convertCapacity capVarMapping
    match cap with
    | A.CapacityConst (_, value) ->
        T.CapacityConst value
    | A.CapacityNameExpr (_, name) ->
        Map.findDefault name (T.CapacityVar name) capVarMapping
    | A.CapacityOp {left=(_, left); op=(_, op); right=(_, right)} ->
        let left' = convertCapacity left
        let right' = convertCapacity right
        let op' = match op with
                    | A.CapAdd -> T.CapAdd
                    | A.CapDivide -> T.CapDivide
                    | A.CapMultiply -> T.CapMultiply
                    | A.CapSubtract -> T.CapSubtract
        T.CapacityOp {left=left'; op=op'; right=right'}
    | A.CapacityUnaryOp {op=(_, op); term=(_, term)} ->
        let op' = match op with
                    | A.CapNegate -> T.CapNegate
        let term' = convertCapacity term
        T.CapacityUnaryOp {op=op'; term=term'}

let rec typeof ((posE, e) : A.PosAdorn<A.Expr>)
               (dtenv : Map<string * string, T.DeclarationTy>)
               (menv : Map<string, string*string>)
               (localVars : Set<string>)
               (ienv : Map<string * string, int>)
               (tyVarMapping : Map<string, T.TyExpr>)
               (capVarMapping : Map<string, T.CapacityExpr>)
               // First bool represents mutability
               (gamma : Map<string, bool * T.TyScheme>) =
    let getTypes = List.map T.getType

    let convertType' = convertType menv tyVarMapping capVarMapping
    let convertCapacity' = convertCapacity capVarMapping

    // Taus is what the overall pattern's type should equal
    let rec checkPattern (posp, p) tau =
        let mutable gamma' = gamma
        let mutable localVars = Set.empty
        let rec checkPattern' (posp, p) tau =
            let rec checkPatterns pats =
                match pats with
                | [] -> ([], Trivial)
                | (p, tau)::ps ->
                    let (p', c) = checkPattern' p tau
                    let (ps', c') = checkPatterns ps
                    (p'::ps', c &&& c')
            match p with
            | A.MatchTuple (_, pats) ->
                let innerTaus = List.map freshtyvar pats
                let c = tau =~= (T.ConApp (T.TyCon T.TupleTy, innerTaus, []), errStr [posp] "Tuple pattern does not match the expression.")
                let (pats', c') = checkPatterns (List.zip pats innerTaus)
                ((posp, tau, T.MatchTuple pats'), c &&& c')
            | A.MatchFalse _ ->
                ((posp, tau, T.MatchFalse), booltype =~= (tau, errStr [posp] "False pattern does not match the type of the expression."))
            | A.MatchTrue _ ->
                ((posp, tau, T.MatchTrue), booltype =~= (tau, errStr [posp] "True pattern does not match the type of the expression."))
            | A.MatchFloatVal (_, value) ->
                ((posp, tau, T.MatchFloatVal value), floattype =~= (tau, errStr [posp] "Float pattern does not match the type of the expression."))
            | A.MatchIntVal (_, value) ->
                ((posp, tau, T.MatchIntVal value), int32type =~= (tau, errStr [posp] "Integer pattern does not match the type of the expression."))
            | A.MatchUnderscore _ ->
                ((posp, tau, T.MatchUnderscore), Trivial)
            | A.MatchUnit (posu, _) ->
                ((posp, tau, T.MatchUnit), unittype =~= (tau, errStr [posu] "Unit pattern does not match the type of the expression."))
            | A.MatchVar { varName=(posv, varName); mutable_=(posm, mutable_); typ=typ } ->
                if Set.contains varName localVars then
                    raise <| TypeError ((errStr [posv] (sprintf "This pattern already contains a variable named %s." varName)).Force())
                else
                    localVars <- Set.add varName localVars
                    // NOTICE THAT WE DO NOT GENERALIZE HERE
                    // This is what makes this type system different from
                    // Hindley Milner
                    gamma' <- Map.add varName (mutable_, T.Forall ([], [], tau)) gamma'
                    let c' = match typ with
                             | Some (post, typ) ->
                                 tau =~= (convertType' typ, errStr [post] "Type constraint in pattern could not be satisfied")
                             | None ->
                                Trivial
                    ((posp, tau, T.MatchVar { varName=varName; mutable_=mutable_; typ=tau}), c')
            | A.MatchRecCon {name=(posn, decRef); template=template; fields=(posf, fields)} ->
                let modQual =
                    match decRef with
                    | Choice1Of2 name ->
                        match Map.tryFind name menv with
                        | Some (mod_, name') ->
                            {T.ModQualifierRec.module_ = mod_; T.ModQualifierRec.name = name'}
                        | None ->
                            raise <| TypeError ((errStr [posn] (sprintf "Unable to find record declaration named %s." name)).Force())
                    | Choice2Of2 {module_ = mod_; name=name} ->
                        {T.ModQualifierRec.module_ = A.unwrap mod_; T.ModQualifierRec.name=A.unwrap name}
                let {T.ModQualifierRec.module_=module_; T.ModQualifierRec.name=name} = modQual
                // Lookup a record in dtenv
                match Map.tryFind (module_, name) dtenv with
                | Some dec ->
                    match dec with
                    | T.RecordDecTy (taus, caps, fieldTaus) ->
                        let fieldNamesInDec = Map.keys fieldTaus
                        let fieldNamesInPattern = fields |> List.map (fst >> A.unwrap) |> Set.ofList
                        if Set.isSubset fieldNamesInPattern fieldNamesInDec then
                            let (taus', caps') =
                                match template with
                                | Some (postemp, {tyExprs=(post, tyExprs); capExprs=(posc, capExprs)}) ->
                                    (List.map (A.unwrap >> convertType') tyExprs,
                                     List.map (A.unwrap >> convertCapacity') capExprs)
                                | None ->
                                    (List.map Constraint.freshtyvar taus,
                                     List.map Constraint.freshcapvar caps)
                            let substitution =
                                List.zip taus taus' |> Map.ofList
                            let capSubstitution =
                                List.zip caps caps' |> Map.ofList
                            let freshRecordInstance =
                                Map.map
                                    (fun fieldName fieldTau ->
                                        Constraint.tycapsubst substitution capSubstitution fieldTau)
                                    fieldTaus
                            let pats =
                                List.map
                                    (fun ((_, fieldName), pattern) ->
                                        (pattern, Map.find fieldName freshRecordInstance))
                                    fields
                            let comparisonTau =
                                let b = T.TyCon (T.ModuleQualifierTy modQual)
                                if List.isEmpty taus then
                                    b
                                else
                                    T.ConApp (b, taus', caps')
                            let c = comparisonTau =~= (tau, errStr [posp] "Record pattern did not match expression.")
                            let (pats', c') = checkPatterns pats
                            ((posp, tau, T.MatchRecCon {typ=modQual; fields=List.zip (List.map (fst >> A.unwrap) fields) pats'}), c')
                        else
                            let diff = Set.difference fieldNamesInPattern fieldNamesInDec
                            let diffStr = String.concat ", " diff
                            raise <| TypeError ((errStr [posf] (sprintf "The following fields in the pattern could not be found in the record declaration: %s" diffStr)).Force())
                    | _ -> raise <| TypeError ((errStr [posn] (sprintf "Found a declaration named %s in module %s, but it was not a record declaration." name module_)).Force())
                | None ->
                    raise <| TypeError ((errStr [posn] (sprintf "Unable to find record declaration named %s in module %s" name module_)).Force())
            | A.MatchValCon {name=(posn, decref); template=template; innerPattern=maybeInnerPattern} ->
                let modQual =
                    match decref with
                    | Choice1Of2 name ->
                        if Set.contains name localVars then
                            raise <| TypeError ((errStr [posn] (sprintf "%s is a local variable and not a value constructor." name)).Force())
                        else
                            match Map.tryFind name menv with
                            | Some (mod_, name') ->
                                {T.ModQualifierRec.module_ = mod_; T.ModQualifierRec.name=name'}
                            | None ->
                                raise <| TypeError ((errStr [posn] (sprintf "Unable to find value constructor named %s." name)).Force())
                    | Choice2Of2 {module_ = mod_; name=name} ->
                        {T.ModQualifierRec.module_=A.unwrap mod_; T.ModQualifierRec.name=A.unwrap name}
                let {T.ModQualifierRec.module_=module_; T.ModQualifierRec.name=name} = modQual
                // Lookup a value constructor in dtenv
                match Map.tryFind (module_, name) dtenv with
                | Some (T.FunDecTy valueConstructor) ->
                    let id = Map.find (module_, name) ienv
                    let inst =
                        match template with
                        | Some (post, {tyExprs=(posm, tyExprs); capExprs=(posn, capExprs)}) ->
                            instantiate valueConstructor (List.map (A.unwrap >> convertType') tyExprs) (List.map (A.unwrap >> convertCapacity') capExprs)
                        | None ->
                            freshInstance valueConstructor
                    match inst with
                    | T.ConApp (T.TyCon T.FunTy, returnTau::argTaus, _) ->
                        match (argTaus, maybeInnerPattern) with
                        | ([], None) ->
                            ((posp, tau, T.MatchValCon {modQualifier=modQual; innerPattern=None; id=id}), returnTau =~= (tau, errStr [posn] "Value constructor pattern type does not match the expression."))
                        | ([valueConTau], Some innerPattern) ->
                            let c = returnTau =~= (tau, errStr [posn] "Value constructor pattern type does not match expression.")
                            let (innerPattern', c') = checkPattern' innerPattern valueConTau
                            ((posp, tau, T.MatchValCon {modQualifier=modQual; innerPattern=Some innerPattern'; id=id}), c &&& c')
                        | ([_], None) ->
                            raise <| TypeError ((errStr [posn] (sprintf "Value constructor named %s does not take in an argument, but there was one inner pattern within the pattern match." name)).Force())
                        | ([], Some _) ->
                            raise <| TypeError ((errStr [posn] (sprintf "Value constructor named %s takes in an argument, but there were no inner patterns within the pattern match." name)).Force())
                        | _ ->
                            raise <| TypeError ((errStr [posn] (sprintf "Found declaration named %s, but it wasn't a value constructor." name)).Force())
                    | _ ->
                        raise <| TypeError ((errStr [posn] (sprintf "Found declaration named %s, but it wasn't a value constructor." name)).Force())
                | _ ->
                    raise <| TypeError ((errStr [posn] (sprintf "Unable to find value constructor named %s" name)).Force())
        let (pattern', c) = checkPattern' (posp, p) tau
        (pattern', c, localVars, gamma')
            
    and typesof exprs dtenv menv localVars gamma =
        match exprs with
        | [] -> ([], Trivial)
        | e::es ->
            let (tau, c) = typeof e dtenv menv localVars ienv tyVarMapping capVarMapping gamma
            let (taus, c') = typesof es dtenv menv localVars gamma
            (tau::taus, c &&& c')
    and ty ((posE, expr) : A.PosAdorn<A.Expr>) : (T.TyAdorn<T.Expr> * Constraint) =
        let adorn pos tau expr con =
            ((pos, tau, expr), con)
        match expr with
        | A.UnitExp (pos, ()) ->
            adorn posE unittype T.UnitExp Trivial
        | A.InlineCode (pos, code) ->
            adorn posE unittype (T.InlineCode code) Trivial
        | A.TrueExp (pos, ()) ->
            adorn posE booltype T.TrueExp Trivial
        | A.FalseExp (pos, ()) ->
            adorn posE booltype T.FalseExp Trivial
        | A.IntExp (pos, num) ->
            adorn posE int32type (T.IntExp num) Trivial
        | A.Int8Exp (pos, num) ->
            adorn posE int8type (T.Int8Exp num) Trivial
        | A.Int16Exp (pos, num) ->
            adorn posE int16type (T.Int16Exp num) Trivial
        | A.Int32Exp (pos, num) ->
            adorn posE int32type (T.Int32Exp num) Trivial
        | A.Int64Exp (pos, num) ->
            adorn posE int64type (T.Int64Exp num) Trivial
        | A.UInt8Exp (pos, num) ->
            adorn posE uint8type (T.UInt8Exp num) Trivial
        | A.UInt16Exp (pos, num) ->
            adorn posE uint16type (T.UInt16Exp num) Trivial
        | A.UInt32Exp (pos, num) ->
            adorn posE uint32type (T.UInt32Exp num) Trivial
        | A.UInt64Exp (pos, num) ->
            adorn posE uint64type (T.UInt64Exp num) Trivial
        | A.FloatExp (pos, num) ->
            adorn posE floattype (T.FloatExp num) Trivial
        | A.DoubleExp (pos, num) ->
            adorn posE doubletype (T.DoubleExp num) Trivial
        | A.NullExp (pos, ()) ->
            adorn posE pointertype T.NullExp Trivial
        | A.IfElseExp {condition=(posc, _) as condition; trueBranch=(post, _) as trueBranch; falseBranch=(posf, _) as falseBranch} ->
            let (exprs', c) = typesof [condition; trueBranch; falseBranch] dtenv menv localVars gamma
            let [condition'; trueBranch'; falseBranch'] = exprs'
            let [tauC; tauT; tauF] = getTypes exprs'
            let c' = c &&&
                        (tauC =~= (booltype, errStr [posc] "Condition of if statement expected to be type bool")) &&&
                        (tauT =~= (tauF, errStr [post; posf] "Branches of if statement expected to be of the same type"))
            adorn posE tauT (T.IfElseExp {condition=condition'; trueBranch=trueBranch'; falseBranch=falseBranch'}) c'
        | A.VarExp (posn, varName) ->
            match Map.tryFind varName gamma with
            | Some (_, tyscheme) ->
                adorn posE (freshInstance tyscheme) (T.VarExp varName) Trivial
            | None ->
                raise <| TypeError ((errStr [posn] (sprintf "Variable named %s could not be found" varName)).Force())
        | A.ArrayAccessExp { array=(posa, _) as array; index=(posi, _) as index } ->
            let (exprs', c) = typesof [array; index] dtenv menv localVars gamma
            let [array'; index'] = exprs'
            let [tauA; tauI] = getTypes exprs'
            let tauElement = freshtyvar ()
            let arraySize = freshcapvar ()
            let tauArray = T.ConApp (T.TyCon T.ArrayTy, [tauElement], [arraySize])
            let c' = c &&& (tauA =~= (tauArray, errStr [posa] "An array access expression must access a value of an array type")) &&&
                           (tauI =~= (int32type, errStr [posi] "Expected index of array access expression to have integer type"))
            adorn posE tauElement (T.ArrayAccessExp {array=array'; index=index'}) c'
        | A.ArrayLitExp (posa, exprs) ->
            let (exprs', c) = typesof exprs dtenv menv localVars gamma
            let tauElement = freshtyvar ()
            let c' = List.fold (&&&) c (List.map (flip (T.getType >> (=~=)) (tauElement, errStr [posa] "Expected all elements of array to be of the same type")) exprs')
            let tauArray = T.ConApp (T.TyCon T.ArrayTy, [tauElement], [T.CapacityConst <| int64 (List.length exprs)])
            adorn posE tauArray (T.ArrayLitExp exprs') c'
        | A.ArrayMakeExp {typ=(post, typ); initializer=maybeInitializer} ->
            let typ' = convertType' typ
            match typ' with
            | T.ConApp (T.TyCon T.ArrayTy, [tauElement], [cap]) ->
                let (maybeInitializer', c) =
                    match maybeInitializer with
                    | Some ((posi, _) as initializer) ->
                        let (initializer', c) = ty initializer
                        let c' = c &&& (T.getType initializer' =~= (tauElement, errStr [post; posi] "Expected initializer to have the same type as the type declaration."))
                        (Some initializer', c)
                    | None ->
                        (None, Trivial)
                adorn posE typ' (T.ArrayMakeExp {typ=typ'; initializer=maybeInitializer'}) c
            | _ ->
                raise <| TypeError ((errStr [post] "Type declaration should be an array type").Force())
        | A.AssignExp {left=(posl, left); right=(posr, _) as right; ref=(posref, ref)} ->
            let rec checkLeft left =
                let ((_, taul, left'), c) =
                    match left with
                    | A.ModQualifierMutation (posmq, {module_=(posm, module_); name=(posn, name)}) ->                    
                        match Map.tryFind (module_, name) dtenv with
                        | Some (T.LetDecTy tau) ->
                            if ref then
                                // TODO: Update this if we decide to make module level values mutable
                                adorn posl tau (T.ModQualifierMutation {module_=module_; name=name}) Trivial
                            else
                                raise <| TypeError ((errStr [posmq] "Top level let declarations are not mutable. Did you mean to use 'set ref' instead?").Force())
                        | Some _ ->
                            raise <| TypeError ((errStr [posn] (sprintf "Found a declaration named %s in module %s, but it was not a let declaration." name module_)).Force())
                        | None ->
                            raise <| TypeError ((errStr [posmq] (sprintf "Unable to find a let declaration named %s in module %s." name module_)).Force())
                    | A.ArrayMutation {array=(posa, array); index=(posi, _) as index} ->
                        let elementTau = freshtyvar ()
                        let capVar = freshcapvar ()
                        let (array', c1) = checkLeft array
                        let (index', c2) = ty index
                        let c' = c1 &&& c2 &&& (int32type =~= (T.getType index', errStr [] "")) &&&
                                               (T.ConApp (T.TyCon T.ArrayTy, [elementTau], [capVar]) =~= (T.getType array', errStr [posa] "Expected an array type to perform an array mutation upon"))
                        adorn posl elementTau (T.ArrayMutation {array=T.unwrap array'; index=index'}) c'
                    | A.RecordMutation {record=(posr, record); fieldName=(posf, fieldName)} ->
                        // TODO: Figure out what to do with field names here
                        let fieldTau = freshtyvar ()
                        let (record', c) = checkLeft record
                        adorn posl fieldTau (T.RecordMutation {record=T.unwrap record'; fieldName=fieldName}) c
                    | A.VarMutation (posn, name) ->
                        match Map.tryFind name gamma with
                        | Some (isMutable, tyscheme) ->
                            if ref || isMutable then
                                let tau = freshInstance tyscheme
                                adorn posl tau (T.VarMutation name) Trivial
                            else
                                raise <| TypeError ((errStr [posn] (sprintf "The variable named %s is not mutable." name)).Force())
                        | None ->
                            raise <| TypeError ((errStr [posn] (sprintf "Unable to find variable named %s in the current scope." name)).Force())
                let (rettau, c') =
                    if ref then
                        let tau = freshtyvar ()
                        (tau, c &&& (taul =~= (T.ConApp (T.TyCon T.RefTy, [tau], []), errStr [posl] "The left hand side of the set operation is not a reference, but 'set ref' was used. Do you mean to use just 'set' instead?")))
                    else
                        (taul, c)
                adorn posl rettau left' c'
            // End checkleft
            let (right', c1) = ty right
            let (left', c2) = checkLeft left
            let c' = c1 &&& c2 &&& (T.getType left' =~= (T.getType right', (errStr [posl; posr] "The type of the left hand side should match the type of the right hand side in a set expression.")))
            adorn posE (T.getType right') (T.AssignExp {left=left'; right=right'; ref=ref}) c'
        | A.BinaryOpExp {left=(posl, _) as left; op=(poso, op); right=(posr, _) as right} ->
            let op' =
                match op with
                | A.Add -> T.Add
                | A.BitshiftLeft -> T.BitshiftLeft
                | A.BitshiftRight -> T.BitshiftRight
                | A.BitwiseAnd -> T.BitwiseAnd
                | A.BitwiseOr -> T.BitwiseOr
                | A.BitwiseXor -> T.BitwiseXor
                | A.Divide -> T.Divide
                | A.Equal -> T.Equal
                | A.Greater -> T.Greater
                | A.GreaterOrEqual -> T.GreaterOrEqual
                | A.Less -> T.Less
                | A.LessOrEqual -> T.LessOrEqual
                | A.LogicalAnd -> T.LogicalAnd
                | A.LogicalOr -> T.LogicalOr
                | A.Modulo -> T.Modulo
                | A.Multiply -> T.Multiply
                | A.NotEqual -> T.NotEqual
                | A.Subtract -> T.Subtract
            let (left', c1) = ty left
            let (right', c2) = ty right
            let c' = c1 &&& c2
            let b' = T.BinaryOpExp {left=left'; op=op'; right=right'}
            match op with
            | (A.LogicalAnd | A.LogicalOr) ->
                let c'' = c' &&& (booltype =~= (T.getType left', errStr [posl] "Left hand side of binary expression should be of type boolean")) &&&
                                 (booltype =~= (T.getType right', errStr [posr] "Right hand side of binary expression should be of type boolean"))
                adorn posE booltype b' c''
            | (A.Equal | A.NotEqual) ->
                let c'' = c' &&& Trivial // (T.getType left' =~= (T.getType right', errStr [posl; posr] "Left hand side and right hand side of binary expression should be the same type"))
                adorn posE booltype b' c''
            | (A.Greater | A.GreaterOrEqual | A.Less | A.LessOrEqual) ->
                // TODO: Check numbers somehow
                let c'' = c' &&& ((T.getType left') =~= (T.getType right', errStr [posl; posr] "Left and right hand must be of the same type for this operation"))
                adorn posE booltype b' c''
            | (A.Add | A.BitshiftLeft | A.BitshiftRight | A.BitwiseAnd | A.BitwiseOr | A.BitwiseXor | A.Divide | A.Modulo | A.Multiply | A.Subtract) ->
                // TODO: Check numbers somehow
                let c'' = c' &&& ((T.getType left') =~= (T.getType right', errStr [posl; posr] "Left and right hand must be of the same type for this operation"))
                adorn posE (T.getType left') b' c''
        | A.CallExp {func=(posf, _) as func; args=(posa, args)} ->
            let (func', c1) = ty func
            let (args', c2) = typesof args dtenv menv localVars gamma
            let returnTau = freshtyvar ()
            let placeholders = List.map freshtyvar args
            let c3 = T.ConApp (T.TyCon T.FunTy, returnTau::placeholders, []) =~= (T.getType func', errStr [posf; posa] "The function being called does not have a function type or the number of parameters passed to the function is incorrect.")
            let c4 =
                List.map
                    (fun ((posa, _), arg', placeholder) ->
                        placeholder =~= (T.getType arg', errStr [posa] "The type of the argument is incorrect."))
                    (List.zip3 args args' placeholders)
            let c' = c1 &&& c2 &&& c3 &&& (List.fold (&&&) Trivial c4)
            adorn posE returnTau (T.CallExp {func=func'; args=args'}) c'
        | A.CaseExp {on=(poso, _) as on; clauses=(posc, clauses)} ->
            let (on', c1) = ty on
            let (clauses', c2) =
                List.map
                    (fun (pattern, ((pose, _) as expr)) ->
                        let (pattern', c1, localVars1, gamma') = checkPattern pattern (T.getType on')
                        let localVars' = Set.union localVars localVars1
                        let (expr', c2) = typeof expr dtenv menv localVars' ienv tyVarMapping capVarMapping gamma'
                        let c' = c1 &&& c2
                        ((pattern', expr'), c'))
                    clauses |>
                List.unzip
            match (List.map (snd >> A.getPos) clauses, List.map (snd >> T.getType) clauses') with
            | (firstClausePos::otherClausesPos, firstClauseTau::otherClausesTaus) ->
                let c3 =
                    List.zip otherClausesPos otherClausesTaus |>
                    List.map
                        (fun (pos, clauseTau) ->
                            firstClauseTau =~= (clauseTau, errStr [pos] "All clauses in case expression should have the same type.")) |>
                    List.fold (&&&) Trivial
                let c' = List.fold (&&&) Trivial ((c1 &&& c3)::c2)
                adorn posE firstClauseTau (T.CaseExp {on=on'; clauses=clauses'}) c'
            | _ ->
                raise <| TypeError ((errStr [posc] "No clauses were found in the case statement").Force())
        | A.DerefExp ((pose, _) as exp) ->
            let (exp', c) = ty exp
            let retTau = freshtyvar ()
            let c' = c &&& (T.ConApp (T.TyCon T.RefTy, [retTau], []) =~= (T.getType exp', errStr [pose] "Attempting to dereference an expression with a non-ref type."))
            adorn posE retTau (T.DerefExp exp') c'
        | A.DoWhileLoopExp {condition=(posc, _) as condition; body=(posb, _) as body} ->
            let (body', c1) = ty body
            let (condition', c2) = ty condition
            let c' = c1 &&& c2 &&& (T.getType condition' =~= (booltype, errStr [posc] "Condition of do while loop must be of boolean type")) &&&
                                   (T.getType body' =~= (unittype, errStr [posb] "Body of do while loop must return type unit"))
            adorn posE unittype (T.DoWhileLoopExp {condition=condition'; body=body'}) c'
        | A.WhileLoopExp {condition=(posc, _) as condition; body=(posb, _) as body} ->
            let (body', c1) = ty body
            let (condition', c2) = ty condition
            let c' = c1 &&& c2 &&& (T.getType condition' =~= (booltype, errStr [posc] "Condition of while loop must be of boolean type")) &&&
                                   (T.getType body' =~= (unittype, errStr [posb] "Body of while loop must return type unit"))
            adorn posE unittype (T.WhileLoopExp {condition=condition'; body=body'}) c'
        | A.ForLoopExp {typ=maybeTyp; varName=(posv, varName); start=(poss, _) as start; direction=(posd, direction); body=(posb, _) as body; end_=(pose, _) as end_} ->
            let direction' =
                match direction with
                | A.Upto -> T.Upto
                | A.Downto -> T.Downto
            let tauIterator =
                match maybeTyp with
                | Some (_, tau) ->
                    convertType' tau
                | None ->
                    int32type
            let (start', c1) = ty start
            let (end_', c2) = ty end_
            let gamma' = Map.add varName (false, T.Forall ([], [], tauIterator)) gamma
            let (body', c3) = typeof body dtenv menv (Set.add varName localVars) ienv tyVarMapping capVarMapping gamma'
            let c' = c1 &&& c2 &&& (tauIterator =~= (T.getType start', errStr [posv; poss] "Type of the start expression does not match the type of the iterator")) &&&
                                   (tauIterator =~= (T.getType end_', errStr [posv; pose] "Type of the end expression doesn't match the type of the iterator")) &&&
                                   (T.getType body' =~= (unittype, errStr [posb] "Body of do while loop must return type unit"))
            adorn posE unittype (T.ForLoopExp {typ=tauIterator; varName=varName; start=start'; end_=end_'; body=body'; direction=direction'}) c'
        | A.LambdaExp (posf, {returnTy=maybeReturnTy; arguments=(posargs, arguments); body=(posb, _) as body}) ->
            let (gamma1Lst, c1s, localVars1, arguments') =
                arguments |>
                List.map
                    (fun ((posa, argName), maybeArgTau) ->
                        let tau = freshtyvar ()
                        let argConstraint =
                            match maybeArgTau with
                            | Some (post, tauConstraint) ->
                                convertType' tauConstraint =~= (tau, errStr [post] "Invalid argument type constraint")
                            | None ->
                                Trivial
                        let gammaEntry = (argName, (false, T.Forall ([], [], tau)))
                        (gammaEntry, argConstraint, argName, (argName, tau))) |>
                List.unzip4
            let gamma' = Map.merge gamma (Map.ofList gamma1Lst)
            let c1 = List.fold (&&&) Trivial c1s
            let localVars' = Set.union localVars (Set.ofList localVars1)
            let (body', c2) = typeof body dtenv menv localVars' ienv tyVarMapping capVarMapping gamma'
            let c3 = 
                match maybeReturnTy with
                | Some (posr, returnTau) ->
                    convertType' returnTau =~= (T.getType body', errStr [posr] "Invalid return type constraint")
                | None ->
                    Trivial
            let lambdaTau = T.ConApp ((T.TyCon T.FunTy), (T.getType body')::(List.map snd arguments'), [])
            let c' = c1 &&& c2 &&& c3
            adorn posE lambdaTau (T.LambdaExp {returnTy=T.getType body'; arguments=arguments'; body=body'}) c'
        // Hit a let expression that is not part of a sequence
        // In this case its variable bindings are useless, but the right hand side might still
        // produce side effects
        // We also have to make sure that the pattern matching agrees with the type of the right
        | A.LetExp {left=left; right=(posr, _) as right} ->
            let (right', c1) = ty right
            let (left', c2, _, _) = checkPattern left (T.getType right')
            let c' = c1 &&& c2
            adorn posE (T.getType right') (T.LetExp {left=left'; right=right'}) c'
        | A.ModQualifierExp (posmq, {module_=(pos, module_); name=(posn, name)}) ->
            let tau =
                match Map.tryFind (module_, name) dtenv with
                | Some (T.FunDecTy tyscheme) ->
                    freshInstance tyscheme
                | Some (T.LetDecTy tau) ->
                    tau
                | Some (T.RecordDecTy _) ->
                    raise <| TypeError ((errStr [posmq] (sprintf "Found declaration named %s in module %s, but it was a record declaration and not a value declaration." name module_)).Force())
                | Some (T.UnionDecTy _) ->
                    raise <| TypeError ((errStr [posmq] (sprintf "Found declaration named %s in module %s, but it was an algebraic datatype declaration and not a value declaration." name module_)).Force())
                | None ->
                    raise <| TypeError ((errStr [posmq] (sprintf "Unable to find declaration named %s in module %s." name module_)).Force())
            adorn posE tau (T.ModQualifierExp {module_=module_; name=name}) Trivial
        | A.QuitExp maybeTau ->
            let tau =
                match maybeTau with
                | Some (post, tau) ->
                    convertType' tau
                | None ->
                    freshtyvar ()
            adorn posE tau (T.QuitExp tau) Trivial
        | A.RecordAccessExp {record=(posr, _) as record; fieldName=(posf, fieldName)} ->
            let (record', c') = ty record
            // TODO: Do something about record access type checking
            let tau = freshtyvar ()
            adorn posE tau (T.RecordAccessExp {record=record'; fieldName=fieldName}) c'
        | A.RecordExp { recordTy=(posr, recordTy); templateArgs=maybeTemplateArgs; initFields=(posi, initFields)} ->
            let (module_, name) =
                match recordTy with
                | Choice1Of2 name ->
                    match Map.tryFind name menv with
                    | Some x ->
                        x
                    | None ->
                        raise <| TypeError ((errStr [posr] (sprintf "Unable to find record named %s in the current scope." name)).Force())
                | Choice2Of2 {module_=(posm, module_); name=(posn, name)} ->
                    (module_, name)
                | _ ->
                    raise <| TypeError ((errStr [posr] (sprintf "Invalid type expression in record expression")).Force())
            match Map.tryFind (module_, name) dtenv with
            | Some declarationTy ->
                match declarationTy with
                | T.RecordDecTy (tyvars, capvars, defFields) ->
                    let initFieldNames = initFields |> List.map (fst >> A.unwrap)
                    if List.hasDuplicates initFieldNames then
                        raise <| TypeError ((errStr [posi] "Duplicate fields in record expression.").Force())
                    else
                        ()
                    let initFieldNamesSet = Set.ofList initFieldNames
                    let defFieldNames = Map.keys defFields
                    let nameDiff = Set.difference defFieldNames (Set.ofList initFieldNames)
                    if Set.isEmpty nameDiff then
                        ()
                    else
                        let missingFields = String.concat ", " nameDiff
                        raise <| TypeError ((errStr [posi] (sprintf "Type error: Missing fields named %s from record expression." missingFields)).Force())
                    let (substitution, capSubstitution) =
                        match maybeTemplateArgs with
                        // Explicit template instantiation
                        | Some (post, {tyExprs=(postyexprs, tyExprs); capExprs=(posc, capExprs)}) ->
                            (tyExprs |> List.map (A.unwrap >> convertType'),
                             capExprs |> List.map (A.unwrap >> convertCapacity'))
                        | None ->
                            (List.map freshtyvar tyvars,
                             List.map freshcapvar capvars)
                    let tau =
                        let t1 = T.TyCon (T.ModuleQualifierTy {module_=module_; name=name})
                        if List.isEmpty substitution then
                            t1
                        else
                            T.ConApp (t1, substitution, capSubstitution)
                    let recordDecTy = instantiateRecord (tyvars, capvars, defFields) substitution capSubstitution
                    let (fieldExprs', c1) =
                        initFields |>
                        List.map
                            (fun ((posn, fieldName), ((pose, _) as fieldExpr)) ->
                                let (fieldExpr', c1) = ty fieldExpr
                                match Map.tryFind fieldName recordDecTy with
                                | Some tau ->
                                    let c' = c1 &&& (tau =~= (T.getType fieldExpr', errStr [pose] "Type error: Type of expression does not match the type of the field given in the record declaration."))
                                    ((fieldName, fieldExpr'), c')
                                | None ->
                                    raise <| TypeError ((errStr [posn] (sprintf "Unable to find field named %s in record declaration." fieldName)).Force())) |>
                        List.unzip
                    let c' = List.fold (&&&) Trivial c1
                    let templateArgs' =
                        if List.isEmpty substitution then
                            None
                        else
                            Some ({tyExprs=substitution; capExprs=capSubstitution} : T.TemplateApply)
                    adorn posE tau (T.RecordExp {recordTy={module_=module_; name=name}; templateArgs=templateArgs'; initFields=fieldExprs'}) c'
                | _ ->
                    raise <| TypeError ((errStr [posr] (sprintf "Found a declaration named %s in module %s, but it was not a record type." name module_)).Force())
            | None ->
                raise <| TypeError ((errStr [posr] (sprintf "Unable to find record type declaration named %s in module %s" name module_)).Force())
        | A.RefExp ((pose, _) as expr) ->
            let (expr', c') = ty expr
            let tau = T.ConApp ((T.TyCon T.RefTy), [T.getType expr'], [])
            adorn posE tau (T.RefExp expr') c'
        | A.SequenceExp (poss, exps) ->
            let ((pose, _) as exp)::rest = exps
            let (exp', c1) = ty exp
            let (localVars', gamma') =
                match exp with
                | (_, A.LetExp {left=left; right=right}) ->
                    // The constraints are already included in c1 above
                    let (_, _, localVars', gamma') = checkPattern left (T.getType exp')
                    (Set.union localVars localVars', gamma')
                | _ ->
                    (localVars, gamma)

            let (tau, rest', c2)  =
                if List.isEmpty rest then
                    // Last thing in the sequence
                    // so the type of the sequence is the type
                    // of the expression
                    (T.getType exp', [], Trivial)
                else
                    // Not the last thing in the sequence
                    // so the type of the sequence is the type
                    // of the rest
                    let ((_, tau, T.SequenceExp rest'), c2) = typeof (poss, A.SequenceExp (poss, rest)) dtenv menv localVars' ienv tyVarMapping capVarMapping gamma'
                    (tau, rest', c2)
                    
            let c' = c1 &&& c2
            adorn posE tau (T.SequenceExp (exp'::rest')) c'
        | A.TemplateApplyExp {func=(posf, func); templateArgs=(post, {tyExprs=(postyexprs, tyExprs); capExprs=(posc, capExprs)})} ->            
            let (func', scheme, decrefs) =
                match func with
                | Choice1Of2 name ->
                    match Map.tryFind name gamma with
                    | Some (_, scheme) ->
                        let decrefs =
                            if Set.contains name localVars then
                                Set.empty
                            else
                                let (module_, name) = Map.find name menv
                                Set.singleton ({module_=module_; name=name} : T.ModQualifierRec)
                        (Choice1Of2 name, scheme, decrefs)  
                    | None ->
                        raise <| TypeError ((errStr [posf] (sprintf "Unable to find function named '%s' in the current scope." name)).Force())
                | Choice2Of2 {module_=(posm, module_); name=(posn, name)} ->
                    match Map.tryFind (module_, name) dtenv with
                    | Some (T.FunDecTy scheme) ->
                        (Choice2Of2 ({module_=module_; name=name} : T.ModQualifierRec), scheme, Set.singleton {module_=module_; name=name})
                    | Some _ ->
                        raise <| TypeError ((errStr [posf] (sprintf "Found declaration named '%s' in module '%s', but it was not a function declaration." name module_)).Force())
                    | None ->
                        raise <| TypeError ((errStr [posf] (sprintf "Unable to find declaration named '%s' in module '%s'" name module_)).Force())
            //let templateArgs' = List.map (A.unwrap >> convertType menv Map.empty Map.empty) tyExprs
            //let templateArgsCaps' = List.map (A.unwrap >> convertCapacity Map.empty) capExprs
            let templateArgs' = List.map (A.unwrap >> convertType') tyExprs
            let templateArgsCaps' = List.map (A.unwrap >> convertCapacity') capExprs
            // TODO: Deal with capacities (again)
            let tau = instantiate scheme templateArgs' templateArgsCaps'
            //let tau = freshInstance scheme
            adorn posE tau (T.TemplateApplyExp {func=func'; templateArgs={tyExprs=templateArgs'; capExprs=templateArgsCaps'}}) Trivial
        | A.TupleExp exprs ->
            let (exprs', c') = typesof exprs dtenv menv localVars gamma
            let subTaus = List.map T.getType exprs'
            let tau = T.ConApp ((T.TyCon T.TupleTy), subTaus, [])
            adorn posE tau (T.TupleExp exprs') c'
        | A.TypeConstraint {exp=(pose, _) as exp; typ=(post, typ)} ->
            let (exp', c1) = ty exp
            let c' = c1 &&& (convertType' typ =~= (T.getType exp', errStr [pose; post] "Type constraint could not be satisfied"))
            adorn posE (T.getType exp') (T.unwrap exp') c'
        | A.UnsafeTypeCast {exp=(pose, _) as exp; typ=(post, typ)} ->
            let (exp', c) = ty exp
            let typ' = convertType' typ
            adorn pose typ' (T.unwrap exp') c
        | A.UnaryOpExp {op=(poso, op); exp=(pose, _) as exp} ->
            let (exp', c1) = ty exp
            let (op', c2, tau) =
                match op with
                | A.LogicalNot ->
                    (T.LogicalNot, booltype =~= (T.getType exp', errStr [pose] "The type of an expression applied to a logical not operation must be a boolean"), booltype)
                | A.BitwiseNot ->
                    (T.BitwiseNot, Trivial, T.getType exp')
                | A.Negate ->
                    (T.Negate, Trivial, T.getType exp')
            let c' = c1 &&& c2
            adorn posE tau (T.UnaryOpExp {op=op'; exp=exp'}) c'
    ty (posE, e)

let rec findFreeVars (theta : Map<string, T.TyExpr>) (kappa : Map<string, T.CapacityExpr>) (e : T.TyAdorn<T.Expr>) : (A.PosAdorn<string> list) * (A.PosAdorn<string> list) =
    let ffv = findFreeVars theta kappa

    let append2 (xs, ys) =
        (List.concat xs, List.concat ys)
    
    let freeVarsTyp pos tau =
        let tau' = Constraint.tycapsubst theta kappa tau
        let (ft0, fc0) = Constraint.freeVars tau'
        let ft = List.ofSeq ft0
        let fc = List.ofSeq fc0
        (List.zip (List.replicate (List.length ft) pos) ft,
         List.zip (List.replicate (List.length fc) pos) fc)
    
    let freeVarsCap pos cap =
        let cap' = Constraint.capsubst kappa cap
        let fc = Constraint.freeCapVars cap' |> List.ofSeq
        ([], List.zip (List.replicate (List.length fc) pos) fc)

    let freeVarsTemplateApply pos ({tyExprs=tyExprs; capExprs=capExprs} : T.TemplateApply) =
        let t = append2 (List.map (freeVarsTyp (T.getPos e)) tyExprs |> List.unzip)
        let c = append2 (List.map (freeVarsCap (T.getPos e)) capExprs |> List.unzip)
        append2 ([t; c] |> List.unzip)

    let rec freeVarsLeftAssign pos left =
        match left with
        | (T.VarMutation _ | T.ModQualifierMutation _) ->
            ([], [])
        | T.ArrayMutation {array=array; index=index} ->
            append2 ([freeVarsLeftAssign pos array; ffv index] |> List.unzip)
        | T.RecordMutation {record=record} ->
            freeVarsLeftAssign pos record

    let rec freeVarsPattern ((pos, _, pat) : T.TyAdorn<T.Pattern>) =
        match pat with
        | T.MatchVar {typ=typ} ->
            freeVarsTyp pos typ
        | (T.MatchIntVal _ | T.MatchFloatVal _ | T.MatchUnit | T.MatchTrue | T.MatchFalse | T.MatchUnderscore | T.MatchValCon {innerPattern=None}) ->
            ([], [])
        | T.MatchValCon {innerPattern=Some innerPattern} ->
            freeVarsPattern innerPattern
        | T.MatchRecCon {fields=fields} ->
            append2 (fields |> List.map (snd >> freeVarsPattern) |> List.unzip)
        | T.MatchTuple pats ->
            append2 (List.map freeVarsPattern pats |> List.unzip)
    
    let (freeTaus, freeCaps) = freeVarsTyp (T.getPos e) (T.getType e)
    let (freeTaus', freeCaps') =
        match T.unwrap e with
        | T.ArrayLitExp exprs ->
            append2 (List.map ffv exprs |> List.unzip)
        | T.ArrayAccessExp {array=array; index=index} ->
            append2 (List.map ffv [array; index] |> List.unzip)
        | T.ArrayMakeExp {typ=typ; initializer=Some initializer} ->
            append2 ([freeVarsTyp (T.getPos e) typ; ffv initializer] |> List.unzip)
        | T.ArrayMakeExp {typ=typ; initializer=None} ->
            freeVarsTyp (T.getPos e) typ
        | T.AssignExp {left=left; right=right} ->
            append2 ([ffv right; freeVarsLeftAssign (T.getPos left) (T.unwrap left)] |> List.unzip)
        | T.BinaryOpExp {left=left; right=right} ->
            append2 ([ffv left; ffv right] |> List.unzip)
        | T.CallExp {func=func; args=args} ->
            append2 (List.map ffv (func::args) |> List.unzip)
        | T.CaseExp {on=on; clauses=clauses} ->
            let pats = append2 (List.map (fst >> freeVarsPattern) clauses |> List.unzip)
            let exprs = append2 (List.map (snd >> ffv) clauses |> List.unzip)
            append2 ([ffv on; pats; exprs] |> List.unzip)
        | T.DerefExp expr ->
            ffv expr
        | T.DoWhileLoopExp {condition=condition; body=body} ->
            append2 ([ffv condition; ffv body] |> List.unzip)
        | (T.FalseExp | T.FloatExp _ | T.InlineCode _ | T.IntExp _ |
            T.InternalDeclareVar _ | T.ModQualifierExp _ | T.NullExp |
            T.TrueExp | T.UnitExp | T.VarExp _) ->
            ([], [])
        | T.ForLoopExp {typ=typ; start=start; end_=end_; body=body} ->
            append2 ([freeVarsTyp (T.getPos e) typ; ffv start; ffv end_; ffv body] |> List.unzip)
        | T.IfElseExp {condition=condition; trueBranch=trueBranch; falseBranch=falseBranch} ->
            append2 (List.map ffv [condition; trueBranch; falseBranch] |> List.unzip)
        | T.LambdaExp {returnTy=returnTy; arguments=arguments; body=body} ->
            let a = append2 (List.map (snd >> freeVarsTyp (T.getPos e)) arguments |> List.unzip)
            append2 ([freeVarsTyp (T.getPos e) returnTy; a; ffv body] |> List.unzip)
        | T.LetExp {left=left; right=right} ->
            append2 ([freeVarsPattern left; ffv right] |> List.unzip)
        | T.QuitExp typ ->
            freeVarsTyp (T.getPos e) typ
        | T.RecordAccessExp {record=record} ->
            ffv record
        | T.RecordExp {templateArgs=None; initFields=initFields} ->
            append2 (List.map (snd >> ffv) initFields |> List.unzip)
        | T.RecordExp {templateArgs=Some templateArgs; initFields=initFields} ->
            let f = append2 (List.map (snd >> ffv) initFields |> List.unzip)
            let t = freeVarsTemplateApply (T.getPos e) templateArgs
            append2 ([f; t] |> List.unzip)
        | T.RefExp exp ->
            ffv exp
        | T.SequenceExp exprs ->
            append2 (List.map ffv exprs |> List.unzip)
        | T.TemplateApplyExp {templateArgs=templateArgs} ->
            freeVarsTemplateApply (T.getPos e) templateArgs
        | T.TupleExp exprs ->
            append2 (List.map ffv exprs |> List.unzip)
        | T.UnaryOpExp {exp=exp} ->
            ffv exp
        | T.WhileLoopExp {condition=condition; body=body} ->
            append2 ([ffv condition; ffv body] |> List.unzip)
    
    (List.append freeTaus freeTaus', List.append freeCaps freeCaps')

// Takes in module's declarations and finds the name of the module
let nameInModule (A.Module decs) =
    let names = List.filter (fun dec -> match dec with
                                            | (_, A.ModuleNameDec _) -> true
                                            | _ -> false) decs
    match names with
        | [(_, A.ModuleNameDec name)] -> Some name
        | _ -> None
        
// Takes in module's declarations and finds the names of the declarations in the module
let declarationsInModule (A.Module decs) =
    let namedDecs = List.filter (fun dec -> match dec with
                                                | (_, A.FunctionDec _) -> true
                                                | (_, A.RecordDec _) -> true
                                                | (_, A.UnionDec _) -> true
                                                | (_, A.LetDec _) -> true
                                                | _ -> false) decs
    List.concat (List.map (fun dec -> match dec with
                                          | (_, A.FunctionDec {name=name}) -> [name]
                                          | (_, A.RecordDec {name=name}) -> [name]
                                          | (_, A.UnionDec {name=name; valCons=valCons}) ->
                                                name::(valCons |> A.unwrap |> List.map fst)
                                          | (_, A.LetDec {varName=name}) -> [name]
                                          | _ -> failwith "This should never happen") namedDecs) |> List.map A.unwrap

// Takes in module's declarations and finds the value declaratin names in the module
let valueDecsInModule (A.Module decs) =
    let namedDecs = List.filter (fun dec -> match dec with
                                                | (_, A.FunctionDec _) -> true
                                                | (_, A.LetDec _) -> true
                                                | _ -> false) decs
    List.map ((fun dec -> match dec with
                             | (_, A.FunctionDec {name=name}) -> name
                             | (_, A.LetDec {varName=name}) -> name
                             | _ -> failwith "This should never happen") >> A.unwrap) namedDecs

let isNamedDec dec = match dec with
                         | (A.RecordDec _ | A.UnionDec _ | A.LetDec _ | A.FunctionDec _) -> true
                         | _ -> false

// Takes in module's declarations and finds the types in the module
let typesInModule (A.Module decs) = 
    let typeDecs = List.filter (fun dec -> match dec with
                                           | (_, A.RecordDec _) -> true
                                           | (_, A.UnionDec _ ) -> true
                                           | _ -> false) decs
    List.map ((fun dec -> match dec with
                         | (_, A.RecordDec {name=name}) -> name
                         | (_, A.UnionDec {name=name}) -> name
                         | _ -> failwith "This should never happen") >> A.unwrap) typeDecs

let opensInModule (A.Module decs) =
    let opens = List.filter (fun dec -> match A.unwrap dec with
                                        | A.OpenDec _ -> true
                                        | _ -> false) decs
    List.concat (List.map (fun dec -> match A.unwrap dec with
                                      |A.OpenDec names -> A.unwrap names
                                      | _ -> failwith "This 0should never happen") opens)

let nameOfDec dec = match dec with
                        | (A.RecordDec {name=name} | A.UnionDec {name=name} | A.LetDec {varName=name} | A.FunctionDec {name=name}) -> name
                        | _ -> failwith "This declaration doesn't have a name"

let isLet dec = match dec with
                | A.LetDec _ -> true
                | _ -> false
let isFunction dec = match dec with
                        | A.FunctionDec _ -> true
                        | _ -> false
let isInclude dec = match dec with
                    | A.IncludeDec _ -> true
                    | _ -> false
let isOpen dec = match dec with
                    | A.OpenDec _ -> true
                    | _ -> false
let isTypeDec dec = match dec with
                    | (A.UnionDec _ | A.RecordDec _) -> true
                    | _ -> false
let isUnionDec dec = match dec with
                     | A.UnionDec _ -> true
                     | _ -> false

let typecheckProgram (program : A.Module list) (fnames : string list) =
    let modNamesToMods =
        let names =
            List.zip program fnames |>
            List.map (fun (module_, fname) ->
                match nameInModule module_ with
                | Some name -> A.unwrap name
                | None -> raise <| SemanticError (sprintf "Semantic error in %s: The module does not contain exactly one module declaration." fname))
        Map.ofList (List.zip names program)
    
    let valueDecsSet =
        program |> List.map (fun decs ->
            let modName = nameInModule decs |> Option.get |> A.unwrap
            let valNames = valueDecsInModule decs
            List.zip
                (List.map (fun _ -> modName) valNames)
                valNames) |> List.concat |> Set.ofList

    let modNamesToMenvs =
        // maps names to module qualifiers
        let menvs0 = (List.map (fun (A.Module decs) ->
            let modName = nameInModule (A.Module decs) |> Option.get |> A.unwrap
            let typeNames = typesInModule (A.Module decs)
            let valNames = valueDecsInModule (A.Module decs)
            // Find the names of all of the value constructors as well
            let valConNames =
                decs |> List.map A.unwrap |> List.filter isUnionDec |>
                List.map
                    (fun (A.UnionDec {valCons=(_, valCons)}) -> valCons |> List.map (fun ((_, name), _) -> name)) |>
                List.concat
            let names = typeNames @ valNames @ valConNames
            match Seq.duplicates names with
            | dups when Seq.length dups = 0 ->
                List.fold (fun map2 name ->
                    Map.add name (modName, name) map2
                ) Map.empty names
            | dups ->
                let dupsStr = String.concat ", " dups
                raise <| SemanticError (sprintf "Semantic error in module %s: The following declarations have duplicate definitions: %s" modName dupsStr)
        ) program)

        let modNamesToMenvs0 = Map.ofList (List.zip (List.map (nameInModule >> Option.get >> A.unwrap) program) menvs0)

        // Merge the menvs together based on the open declarations
        (Map.map (fun modName menv0 ->
            let allOpens = List.map A.unwrap (opensInModule (Map.find modName modNamesToMods))
            List.fold (fun menv1 nameToMerge ->
                match Map.tryFind nameToMerge modNamesToMenvs0 with
                | Some menv' -> Map.merge menv' menv1 
                | None -> raise <| SemanticError (sprintf "Semantic error: Module %s opens %s, which does not exist." modName nameToMerge)
            ) menv0 allOpens
        ) modNamesToMenvs0)
    
    // Maps module qualifiers to their actual declarations
    let denv = (List.fold (fun map (A.Module decs) ->
        let modName = nameInModule (A.Module decs) |> Option.get
        let namedDecs = List.filter (A.unwrap >> isNamedDec) decs
        List.fold (fun map2 dec0 ->
            let decName = nameOfDec (A.unwrap dec0)
            let qual = (A.unwrap modName, A.unwrap decName)
            Map.add qual dec0 map2) map namedDecs
    ) Map.empty program)

    let ienv = (Map.fold (fun accumIenv ((module_, name) as modQual) d ->
        match A.unwrap d with
        | A.UnionDec {valCons=(_, valCons)} ->
            (List.mapi (fun i ((_, valConName), _) ->
                (valConName, i)
            ) valCons) |>
            (List.fold (fun accumIenv' (valConName, i) ->
                Map.add (module_, valConName) i accumIenv')
            accumIenv)
        | _ ->
            accumIenv
    ) Map.empty denv)
    
    let extractFromTemplate maybeTemplate =
        match maybeTemplate with
        | None -> ([], [])
        | Some (_, ({tyVars=(_, tyVars); capVars=maybeCapVars} : A.Template)) ->
            let t = List.map A.unwrap tyVars
            let c =
                match maybeCapVars with
                | None -> []
                | Some (_, capVars) ->
                    List.map A.unwrap capVars
            (t, c)

    let dtenv0 = (Map.fold (fun accumDtenv0 ((module_, name) as modQual) d ->
        let menv = Map.find module_ modNamesToMenvs
        match A.unwrap d with
        | A.RecordDec {fields=(_, fields); template=maybeTemplate} ->
            let (t, c) = extractFromTemplate maybeTemplate
            let fieldMap = fields |> List.map (fun ((_, name), (_, ty)) -> (name, convertType menv Map.empty Map.empty ty)) |> Map.ofList
            Map.add (module_, name) (T.RecordDecTy (t, c, fieldMap)) accumDtenv0
        | A.UnionDec {valCons=(_, valCons); template=maybeTemplate} ->
            let (t, c) = extractFromTemplate maybeTemplate
            let udecty = T.UnionDecTy (t, c, {module_=module_; name=name})
            let retTyBase = T.TyCon <| T.ModuleQualifierTy {module_=module_; name=name}
            let retTy =
                match maybeTemplate with
                | None -> retTyBase
                | Some _ -> T.ConApp (retTyBase, List.map T.TyVar t, List.map T.CapacityVar c)
            let accumDtenv2 = valCons |> (List.fold (fun accumDtenv1 ((_, valConName), maybeTy) ->
                let paramTy = Option.map (A.unwrap >> convertType menv Map.empty Map.empty) maybeTy |> Option.toList
                let ts = T.FunDecTy <| T.Forall (t, c, T.ConApp (T.TyCon T.FunTy, retTy::paramTy, []))
                Map.add (module_, valConName) ts accumDtenv1
            ) accumDtenv0)
            Map.add (module_, name) udecty accumDtenv2
        | _ ->
            accumDtenv0
    ) Map.empty denv)

    // Check the dependency graph first to determine what order we need to typecheck in (topological sort)
    let valueGraph = new QuickGraph.AdjacencyGraph<string*string, QuickGraph.Edge<string*string>>()

    program |> List.iter (fun moduledef ->
        let (A.Module decs) = moduledef
        let module_ = nameInModule moduledef |> Option.get |> A.unwrap
        // List of all let and function declarations in
        // the module currently being considered
        let valueDecs = valueDecsInModule moduledef
        let menv = Map.find module_ modNamesToMenvs
        // Add all the declarations as vertices to the graph
        valueDecs |> List.iter (fun name ->
            valueGraph.AddVertex((module_, name)) |> ignore
        )
        // Find out what declarations this declaration refers to
        valueDecs |> List.iter (fun name ->
            let (pos, dec) = Map.find (module_, name) denv
            let references =
                match dec with
                | (A.FunctionDec {template=template; clause=(_, {body=(_, expr); arguments=(_, arguments)})}) ->
                    let a1 = arguments |> List.map (fst >> A.unwrap) |> Set.ofList
                    // Capacities are local variables as well!
                    let a2 =
                        match template with
                        | Some (_, {capVars=Some (_, capVars)}) ->
                            capVars |> List.map A.unwrap |> Set.ofList
                        | _ -> Set.empty
                    decRefs valueDecsSet menv (Set.union a1 a2) expr
                | A.LetDec {right=(_, expr)} ->
                    decRefs valueDecsSet menv Set.empty expr
            // Add all the edges to the graph
            references |> Set.iter (fun reference ->
                // TODO: Better check here
                if Map.containsKey reference dtenv0 || Map.containsKey reference denv then
                    valueGraph.AddEdge(new QuickGraph.Edge<string*string>((module_, name), reference)) |> ignore
                else
                    raise <| TypeError ((errStr [pos] (sprintf "Reference made to %s:%s which could not be found" (fst reference) (snd reference))).Force())
            )
        )
    )

    let includeDecs = 
        program |>
        List.map (fun (A.Module decs) -> List.filter (A.unwrap >> isInclude) decs) |>
        List.concat |>
        List.map (fun (_, A.IncludeDec (_, includes)) ->
            T.IncludeDec (List.map A.unwrap includes))

    let openDecs = 
        program |>
        List.map (fun (A.Module decs) ->
            let module_ = nameInModule (A.Module decs) |> Option.get |> A.unwrap
            let opens = List.filter (A.unwrap >> isOpen) decs
            let moduleNames = List.map (fun _ -> module_) opens
            List.zip moduleNames opens) |>
        List.concat |>
        List.map (fun (module_, (_, A.OpenDec (_, openModules))) ->
            (module_, T.OpenDec (List.map A.unwrap openModules)))
    
    let moduleNames = program |> List.map (fun decs -> nameInModule decs |> Option.get |> A.unwrap)

    let typeDecs =
        program |>
        List.map (fun (A.Module decs) ->
            let module_ = nameInModule (A.Module decs) |> Option.get |> A.unwrap
            let types = List.filter (A.unwrap >> isTypeDec) decs
            let moduleNames = List.map (fun _ -> module_) types
            List.zip moduleNames types) |>
        List.concat |>
        List.map (fun (module_, (_, dec)) ->
            let menv = Map.find module_ modNamesToMenvs
            match dec with
            | A.UnionDec {name=(_, name); valCons=(_, valCons); template=template} ->
                let valCons' =
                    valCons |> List.map (fun ((_, valConName), maybeType) ->
                        let maybeType' = Option.map (A.unwrap >> (convertType menv Map.empty Map.empty)) maybeType
                        (valConName, maybeType'))
                (module_, T.UnionDec {name=name; template=Option.map (A.unwrap >> convertTemplate) template; valCons=valCons'})
            | A.RecordDec {name=(_, name); template=template; fields=(_, fields)} ->
                let (names, types) = List.unzip fields
                let names' = List.map A.unwrap names
                let types' = List.map (A.unwrap >> convertType menv Map.empty Map.empty) types
                let fields' = List.zip names' types'
                (module_, T.RecordDec {name=name; template=Option.map (A.unwrap >> convertTemplate) template; fields=fields'}))
    
    let (_, connectedComponents) = valueGraph.StronglyConnectedComponents()

    let sccs = connectedComponents |> Map.ofDict |> Map.invertNonInjective |> Map.toList |> List.map snd

    // Now verify that each SCC either contains all functions or just a single let
    sccs |>
    List.iter
        (fun scc ->
            let sccStr = scc |> List.map (fun (m, n) -> sprintf "%s:%s" m n) |> String.concat ", "
            match scc with
            | [x] when isLet (A.unwrap (Map.find x denv)) ->
                ()
            | _ ->
                scc |> List.iter
                    (fun decref ->
                        if isLet (A.unwrap (Map.find decref denv)) then
                            let (module_, name) = decref
                            raise <| TypeError (sprintf "The let named '%s' in module '%s' has a self reference. The following declarations all refer to each other: %s" name module_ sccStr)
                        else
                            ()))
    
    let condensation = valueGraph.CondensateStronglyConnected<_, _, QuickGraph.AdjacencyGraph<_, _>>()
    let dependencyOrder = condensation.TopologicalSort() |> Seq.map (fun scc -> scc.Vertices |> List.ofSeq) |> Seq.rev |> List.ofSeq

    let localGamma globalGamma module_ =
        let menv = Map.find module_ modNamesToMenvs
        (Map.fold (fun gammaAccum localName moduleQual ->
            match Map.tryFind moduleQual globalGamma with
            | Some ty ->
                Map.add localName (false, ty) gammaAccum
            | None ->
                gammaAccum
        ) Map.empty menv)

    let globalGammaInit =
        program |> List.map (fun (A.Module decs) ->
            let module_ = nameInModule (A.Module decs) |> Option.get |> A.unwrap
            decs |> List.map A.unwrap |> List.filter isUnionDec |>
            List.map
                (fun (A.UnionDec {valCons=(_, valCons)}) ->
                    valCons |> List.map (fun ((_, name), _) ->
                        let modqual = (module_, name)
                        let (T.FunDecTy scheme) = Map.find modqual dtenv0
                        (modqual, scheme))) |>
            List.concat) |> List.concat |> Map.ofList

    // TODO: Topological sort for types
    let (checkedDecs, _) =
        dependencyOrder |> List.mapFold
            (fun (dtenv, globalGamma) scc ->
                match scc with
                // Found a SCC containing a single let statement
                | [(module_, name) as modqual] when isLet (A.unwrap (Map.find modqual denv)) ->
                    let (posl, A.LetDec {varName=varName; typ=typ; right=right}) = Map.find modqual denv
                    let menv = Map.find module_ modNamesToMenvs
                    let localVars = Set.empty
                    let gamma = localGamma globalGamma module_
                    let (right', c1) = typeof right dtenv menv localVars ienv Map.empty Map.empty gamma
                    let c2 =
                        match typ with
                        | Some (post, ty) ->
                            T.getType right' =~= (convertType menv Map.empty Map.empty ty, errStr [post; A.getPos right] "The type of the right hand side of the let expression violates the given type constraint.")
                        | None ->
                            Trivial
                    let c = c1 &&& c2
                    let (theta, kappa) = solve c
                    let tau = tycapsubst theta kappa (T.getType right')
                    let elabtau = generalize Set.empty Set.empty tau
                    let globalGamma' = Map.add modqual elabtau globalGamma
                    let dtenv' = Map.add modqual (T.LetDecTy tau) dtenv
                    let let' = T.LetDec {varName=name; typ=tau; right=right'}
                    (([(module_, let')], theta, kappa), (dtenv', globalGamma'))
                // Found a SCC containing mutually recursive function(s)
                | _ ->
                    let alphas = List.map freshtyvar scc
                    let alphaSchemes = List.map (fun a -> T.Forall ([], [], a)) alphas
                    let tempGlobalGamma =
                        List.fold (fun globalGammaAccum (modqual, alphaScheme) ->
                            Map.add modqual alphaScheme globalGammaAccum
                        ) globalGamma (List.zip scc alphaSchemes)
                    let tempGammas = List.map (fst >> localGamma tempGlobalGamma) scc
                    let (funDecsInfo, cs) =
                        List.zip3 scc tempGammas alphas |>
                        List.map
                            (fun ((module_, name) as modqual, tempGamma, alpha) ->
                                let (posf, A.FunctionDec {template=template; clause=(posc, {arguments=(posa, arguments); body=body; returnTy=maybeReturnTy})}) = Map.find modqual denv
                                let menv = Map.find module_ modNamesToMenvs
                                let localArguments = List.map (fst >> A.unwrap) arguments |> Set.ofList
                                if Set.count localArguments = List.length arguments then
                                    ()
                                else
                                    raise <| TypeError ((errStr [posa] "There are duplicate argument names").Force())
                                let (tyVarMapping, capVarMapping, maybeTemplate', localCapacities) =
                                    match template with
                                    // TODO: CHECK THIS
                                    | None -> (Map.empty, Map.empty, None, Set.empty)
                                    | Some (_, {tyVars=(_, tyVars); capVars=maybeCapVars}) ->
                                        let capVars = maybeCapVars |> Option.map A.unwrap |> Option.toList |> List.concat
                                        let tyVars' = List.map freshtyvar tyVars
                                        let tyVars'Names = List.map (fun (T.TyVar name) -> name) tyVars'
                                        let capVars' = List.map freshcapvar capVars
                                        let capVars'Names = List.map (fun (T.CapacityVar name) -> name) capVars'
                                        let t = List.zip (List.map A.unwrap tyVars) tyVars' |> Map.ofList
                                        let c = List.zip (List.map A.unwrap capVars) capVars' |> Map.ofList
                                        let localVars1 = capVars |> List.map A.unwrap |> Set.ofList
                                        let templatePos = (tyVars |> List.map A.getPos, capVars |> List.map A.getPos)
                                        (t, c, Some (({tyVars=tyVars'Names; capVars=capVars'Names} : T.Template), templatePos, capVars), localVars1)
                                let localVars = Set.union localArguments localCapacities
                                // Add the arguments to the type environment (gamma)
                                let (argTys, tempGamma') =
                                    //let tyVarMapping' = Map.map (fun key _ -> freshtyvar ()) tyVarMapping
                                    //let capVarMapping' = Map.map (fun key _ -> freshcapvar ()) capVarMapping
                                    arguments |>
                                    List.mapFold
                                        (fun accumTempGamma' ((posn, name), maybeTy) ->
                                            let argTy = match maybeTy with
                                                        | Some (_, ty) -> convertType menv tyVarMapping capVarMapping ty
                                                        //| Some (_, ty) -> convertType menv tyVarMapping' capVarMapping' ty
                                                        // TODO: Determine if we need to save this tyvar
                                                        | None -> freshtyvar ()
                                            let argTyScheme = T.Forall ([], [], argTy)
                                            (argTy, Map.add name (false, argTyScheme) accumTempGamma'))
                                        tempGamma
                                // Add the capacities to the type environment
                                let tempGamma'' = localCapacities |> (Set.fold (fun accum capVarName ->
                                    Map.add capVarName (false, T.Forall ([], [], int32type)) accum
                                ) tempGamma')
                                //let (post, retTy) =
                                //    match maybeReturnTy with
                                //    | Some (post, ty) -> ([post], convertType menv tyVarMapping capVarMapping ty)
                                //    | None -> ([], freshtyvar ())
                                // Finally typecheck the body
                                let (body', c1) = typeof body dtenv menv localVars ienv tyVarMapping capVarMapping tempGamma''
                                let c2 = alpha =~= (T.ConApp (T.TyCon T.FunTy, (T.getType body')::argTys, []), errStr [posf] "The inferred type of the function violated a constraint based on the function declaration")
                                let c3 =
                                    match maybeReturnTy with
                                    | None -> Trivial
                                    | Some (post, ty) ->
                                        (T.getType body') =~= (convertType menv tyVarMapping capVarMapping ty, errStr [posf; post] "The type of the body did not match the type of the return constraint")
                                let c = c1 &&& c2 &&& c3
                                let argNames = arguments |> List.map (fst >> A.unwrap)
                                ((modqual, maybeTemplate', argNames, argTys, T.getType body', body'), c)) |> List.unzip
                    let c = List.fold (&&&) Trivial cs
                    // Solve the entire SCC at once
                    let (theta, kappa) = solve c
                    let (funDecs', (dtenv', globalGamma')) =
                        funDecsInfo |>
                        List.mapFold
                            (fun (accumDtenv', accumGlobalGamma') ((module_, name) as modqual, maybeTemplate', argNames, argTys, retTy, body') ->
                                let retTy' = tycapsubst theta kappa retTy
                                let argTys' = argTys |> List.map (tycapsubst theta kappa)
                                let arguments' = List.zip argNames argTys'
                                let (t, c, maybeTemplate'', maybeOriginalCapVars) =
                                    match maybeTemplate' with
                                    // TODO: What about inference!
                                    | None -> ([], [], None, None)
                                    | Some ({tyVars=tyVars; capVars=capVars}, (tyVarsPos, capVarsPos), originalCapVars) ->
                                        let tyVars' = List.zip tyVars tyVarsPos |> List.map (fun (tyvar, post) ->
                                            match tycapsubst theta kappa (T.TyVar tyvar) with
                                            | T.TyVar tyvar' ->
                                                tyvar'
                                            | x ->
                                                raise <| TypeError ((errStr [post] (sprintf "The type parameter was inferred to be equivalent to the non-type variable '%s'" (T.typeString x))).Force()))
                                        let capVars' = List.zip capVars capVarsPos |> List.map (fun (capvar, posc) ->
                                            match capsubst kappa (T.CapacityVar capvar) with
                                            | T.CapacityVar capvar' ->
                                                capvar'
                                            | x ->
                                                raise <| TypeError ((errStr [posc] (sprintf "The capacity parameter was inferred to be equivalent to the non-capacity variable '%s'" (T.capacityString x))).Force()))   
                                        (tyVars', capVars, Some ({tyVars=tyVars'; capVars=capVars} : T.Template), Some originalCapVars)
                                let funScheme = T.Forall (t, c, T.ConApp (T.TyCon T.FunTy, retTy'::argTys', []))
                                let body'' =
                                    match maybeOriginalCapVars with
                                    | (None | Some []) ->
                                        body'
                                    | Some originalCapVars ->
                                        let (pos, tau, innerBody) = body'
                                        let saveCapVars =
                                            List.zip originalCapVars c |> List.map (fun ((posc, originalCapVar), newCapVar) ->
                                                (posc, int32type, T.InternalDeclareVar {varName=originalCapVar; typ=int32type; right=(posc, int32type, T.VarExp newCapVar)}))
                                        let innerBody' = T.SequenceExp (saveCapVars @ [body'])
                                        (pos, tau, innerBody')
                                let funDec' = T.FunctionDec {name=name; template=maybeTemplate''; clause={returnTy=retTy'; arguments=arguments'; body=body''}}
                                let accumDtenv'' = Map.add modqual (T.FunDecTy funScheme) accumDtenv'
                                let globalGamma'' = Map.add modqual funScheme accumGlobalGamma'
                                ((module_, funDec'), (accumDtenv'', globalGamma'')))
                            (dtenv, globalGamma)
                    ((funDecs', theta, kappa), (dtenv', globalGamma'))
            ) (dtenv0, globalGammaInit)
    (moduleNames, openDecs, includeDecs, typeDecs, checkedDecs)