module AstAnalysis
module A = Ast
module T = TypedAst
open Extensions
open Error

let rec findUnderscoreTys (tyExpr : A.PosAdorn<A.TyExpr>) : List<FParsec.Position * FParsec.Position> =
    match A.unwrap tyExpr with
    | A.UnderscoreTy und -> [A.getPos und]
    | (A.BaseTy _ | A.CapacityConst _ | A.ModuleQualifierTy _ | A.NameTy _) -> []
    | A.ApplyTy {tyConstructor=tyConstructor; args=(_, args)} ->
        let u1 = findUnderscoreTys tyConstructor
        let u2 = List.map findUnderscoreTys (A.unwrap args)
        u1 @ (List.concat u2)
    | A.ArrayTy {valueType=valueType; capacity=capacity} ->
        (findUnderscoreTys valueType) @ (findUnderscoreTys capacity)
    | A.CapacityOp {left=left; right=right} ->
        (findUnderscoreTys left) @ (findUnderscoreTys right)
    | A.CapacityUnaryOp {term=term} ->
        findUnderscoreTys term
    | A.ClosureTy (_, closureElems) ->
        closureElems |>
        List.map (snd >> findUnderscoreTys) |>
        List.concat
    | A.FunTy {closure=closure; args=args; returnType=returnType} ->
        let u1 = findUnderscoreTys closure
        let u2 = List.map findUnderscoreTys args |> List.concat
        let u3 = findUnderscoreTys returnType
        List.concat [u1; u2; u3]
    | A.RecordTy (_, {fields=(_, fields)}) ->
        fields |> List.map (snd >> findUnderscoreTys) |> List.concat
    | A.RefTy refTy ->
        findUnderscoreTys refTy
    | A.TupleTy elems ->
        elems |> List.map findUnderscoreTys |> List.concat

let resolveUserTyName menv (denv : Map<string * string, A.PosAdorn<A.Declaration>>) (name : string) =
    match Map.tryFind name menv with
    | Some modQual ->
        match Map.tryFind modQual denv with
        | (Some (_, A.AliasDec _)) | (Some (_, A.AlgDataTypeDec _)) ->
            Some modQual
        | _ ->
            None
    | None ->
        None

// Find all types that a type declaration is referring to
let tyRefs (menv : Map<string, string*string>) tyDec =
    let rec refsInTyExpr t =
        match t with
        | A.BaseTy _ ->
            Set.empty
        | A.ModuleQualifierTy {module_=(_, module_); name=(_, name)} ->
            Set.singleton (module_, name)
        | A.ApplyTy {tyConstructor=(_, tyConstructor); args=(_, (_, tyExprs))} ->
            let t1 = refsInTyExpr tyConstructor
            let t2 = List.map (A.unwrap >> refsInTyExpr) tyExprs
            Set.unionMany (t1::t2)
        | A.ArrayTy {valueType=(_, valueType)} ->
            refsInTyExpr valueType
        | A.ClosureTy (_, closureFields) ->
            closureFields |> List.map (snd >> A.unwrap >> refsInTyExpr) |> Set.unionMany
        | A.UnderscoreTy _ ->
            Set.empty
        | A.FunTy {closure=(_, closureTy); args=args; returnType=(_, returnType)} ->
            let t1 = refsInTyExpr closureTy
            let t2 = List.map (A.unwrap >> refsInTyExpr) args |> Set.unionMany
            let t3 = refsInTyExpr returnType
            Set.unionMany [t1; t2; t3]
        | A.NameTy (_, name) ->
            match Map.tryFind name menv with
            | None ->
                Set.empty
            | Some modQual ->
                Set.singleton modQual
        | A.RefTy (_, tau) ->
            refsInTyExpr tau
        | A.TupleTy taus ->
            taus |> List.map (A.unwrap >> refsInTyExpr) |> Set.unionMany
        | A.RecordTy (_, {fields=(_, fields)}) ->
            fields |> List.map (snd >> A.unwrap >> refsInTyExpr) |> Set.unionMany
        | (A.CapacityConst _ | A.CapacityOp _ | A.CapacityUnaryOp _) ->
            Set.empty

    match tyDec with
    | A.AlgDataTypeDec {valCons=(_, valCons)} ->
        valCons |>
        List.map
            (fun (_, tyExprs) ->
                List.map (A.unwrap >> refsInTyExpr) tyExprs |> Set.unionMany) |>
        Set.unionMany
    | A.AliasDec {typ=(_, typ)} ->
        refsInTyExpr typ

let getArgKinds (denv : Map<string * string, A.PosAdorn<A.Declaration>>) posQual ({module_=module_; name=name} : T.ModQualifierRec) =
    match Map.tryFind (module_, name) denv with
    | (Some (_, A.AlgDataTypeDec {template=maybeTemplate}) | Some (_, A.AliasDec {template=maybeTemplate})) ->
        match maybeTemplate with
        | Some (_, template) ->
            List.map snd template
        | None ->
            []
    | Some _ ->
        raise <| SemanticError ((errStr [posQual] (sprintf "Found a declaration with name %s:%s, but it was not an algebraic datatype or alias." module_ name)).Force())
    | None ->
        raise <| SemanticError ((errStr [posQual] (sprintf "Unable to find algebraic datatype or alias with module qualifier %s:%s" module_ name)).Force())

// Separate the arguments by their kinds, given a type constructor and a template to apply to that constructor
// Choice1Of2 indicates a type expression
// Choice2Of2 indicates a capacity expression
let separateArgsByKind (menv : Map<string, string*string>) (denv : Map<string * string, A.PosAdorn<A.Declaration>>) ((posc, tyConstructor) : A.PosAdorn<Ast.TyExpr>) ((posa, args) : Ast.TemplateApply) : (Choice<A.PosAdorn<A.TyExpr>, A.PosAdorn<A.TyExpr>> list) =
    let (module_, name) =
        match tyConstructor with
        | Ast.ModuleQualifierTy {module_=(_, module_); name=(_, name)} ->
            (module_, name)
        | Ast.NameTy (_, name) ->
            match Map.tryFind name menv with
            | Some modQual ->
                modQual
            | None ->
                raise <| SemanticError ((errStr [posc] (sprintf "Unable to find declaration with name %s in the current module environment." name)).Force())
        | _ ->
            raise <| SemanticError ((errStr [posc] "A template can only be applied to a module qualifier or qualified name.").Force())
    let kinds = getArgKinds denv posc {module_=module_; name=name}
    if List.length kinds = List.length args then
        List.zip args kinds |>
        List.map
            (function
            | (arg, A.StarKind _) -> Choice1Of2 arg
            | (arg, A.IntKind _) -> Choice2Of2 arg)
    else
        raise <| SemanticError ((errStr [posc; posa] (sprintf "Incorrect number of template arguments. Expected %d arguments, but got %d instead." (List.length kinds) (List.length args))).Force())

// Get all the variables with the given 'searchKind', given input environments, the type to search through, and the kind of the type
let rec getVars (searchKind : T.Kind) (menv : Map<string, string*string>) (denv : Map<string * string, A.PosAdorn<A.Declaration>>) (tyKind : T.Kind) (ty : Ast.TyExpr) : List<Ast.PosAdorn<string>> =
    let getVars' = getVars searchKind menv denv
    let getVarsMany kind elems = List.map (Ast.unwrap >> getVars' kind) elems |> List.concat
    match ty with
    | Ast.ApplyTy { tyConstructor = tyConstructor; args = (_, args) } ->
        let (tyExprs, capExprs) = Choice.splitChoice2 (separateArgsByKind menv denv tyConstructor args)
        let v1 = getVars' T.StarKind (A.unwrap tyConstructor)
        let v2 = getVarsMany T.StarKind tyExprs
        let v3 = getVarsMany T.IntKind capExprs
        List.concat [v1; v2; v3]
    | Ast.ArrayTy {valueType = (_, valueType); capacity = (_, capacity)} ->
        let v1 = getVars' T.StarKind valueType
        let v2 = getVars' T.IntKind capacity
        v1 @ v2
    | Ast.FunTy {closure = (_, closure); args = args; returnType = (_, returnType)} ->
        let v1 = getVars' T.StarKind closure
        let v2 = getVarsMany T.StarKind args
        let v3 = getVars' T.StarKind returnType
        List.concat [v1; v2; v3]
    | Ast.RefTy (_, refTy) ->
        getVars' T.StarKind refTy
    | Ast.TupleTy elems ->
        getVarsMany T.StarKind elems
    | Ast.RecordTy (_, {fields = (_, fields)}) ->
        fields |> List.map snd |> getVarsMany T.StarKind
    | Ast.ClosureTy (_, fields) ->
        fields |> List.map snd |> getVarsMany T.StarKind
    | (Ast.BaseTy _ | Ast.ModuleQualifierTy _ | Ast.UnderscoreTy _) ->
        []
    | Ast.NameTy name ->
        match (searchKind, tyKind) with
        | (T.IntKind, T.IntKind) ->
            [name]
        | (T.StarKind, T.StarKind) ->
            match resolveUserTyName menv denv (A.unwrap name) with
            | Some _ -> []
            | None -> [name]
        | ((T.StarKind, T.IntKind) | (T.IntKind, T.StarKind)) ->
            []
    | Ast.CapacityOp {left = (_, left); right = (_, right)} ->
        (getVars' T.IntKind left) @ (getVars' T.IntKind right)
    | Ast.CapacityUnaryOp {term = (_, term)} ->
        getVars' T.IntKind term
    | Ast.CapacityConst _ ->
        []

let capVars menv denv tyKind ty = getVars T.IntKind menv denv tyKind ty |> List.map (fun (pos, name) -> (pos, T.CapVar name))
let tyVars menv denv tyKind ty = getVars T.StarKind menv denv tyKind ty |> List.map (fun (pos, name) -> (pos, T.TyVar name))

// Find all top level function and let declarations (value declarations)
// that some expression is referring to
let decRefs valueDecs (menv : Map<string, string*string>) localVars e =
    let rec getVars pattern =
        match pattern with
        | (Ast.MatchFalse _ | Ast.MatchFloatVal _ | Ast.MatchIntVal _ | Ast.MatchTrue _ |
            Ast.MatchUnderscore _ | Ast.MatchUnit _) ->
            Set.empty
        | Ast.MatchRecCon (_, fields) ->
            Set.unionMany (List.map (snd >> Ast.unwrap >> getVars) fields)
        | Ast.MatchTuple (_, elements) ->
            Set.unionMany (List.map (Ast.unwrap >> getVars) elements)
        | Ast.MatchValCon {name=(_, name); innerPattern=(_, innerPattern)} ->
            innerPattern |> List.map (Ast.unwrap >> getVars) |> Set.unionMany
        | Ast.MatchVar {varName=(_, varName)} ->
            Set.singleton varName

    let rec dl localVars l =
        let dl' = dl localVars
        match l with
        | Ast.ArrayMutation {array=(_, array); index=(_, index)} ->
            Set.union (dl' array) (d localVars index)
        | Ast.ModQualifierMutation (_, {module_=(_, module_); name=(_, name)}) ->
            let modqual = (module_, name)
            if Set.contains modqual valueDecs then
                Set.singleton modqual
            else
                Set.empty
        | Ast.RecordMutation {record=(_, record)} ->
            dl' record
        | Ast.RefRecordMutation {recordRef=(_, recordRef)} ->
            d localVars recordRef
        | Ast.VarMutation (_, name) ->
            match Map.tryFind name menv with
            | Some modqual when Set.contains modqual valueDecs ->
                Set.singleton modqual
            | _ -> Set.empty
        | Ast.RefMutation (_, expr) ->
            d localVars expr

    and d localVars e =
        let d' = d localVars
        match e with
        | Ast.ArrayAccessExp {array=(_, array); index=(_, index)} ->
            Set.union (d' array) (d' index)
        | Ast.ArrayLitExp (_, exprs) ->
            Set.unionMany (List.map (Ast.unwrap >> d') exprs)
        | Ast.ArrayMakeExp {initializer=Some (_, initializer)} ->
            d' initializer
        | Ast.ArrayMakeExp _ ->
            Set.empty
        | Ast.AssignExp {left=(_, left); right=(_, right)} ->
            Set.union (dl localVars left) (d' right)
        | Ast.BinaryOpExp {left=(_, left); right=(_, right)} ->
            Set.union (d' left) (d' right)
        | Ast.CallExp {func=(_, func); args=(_, args)} ->
            Set.unionMany ((d' func)::(List.map (Ast.unwrap >> d') args))
        | Ast.CaseExp {on=(_, on); clauses=(_, clauses)} ->
            let s1 = d' on
            let s2 =
                clauses |>
                List.map
                    (fun ((_, pat), (_, expr)) ->
                        let localVars' = Set.union (getVars pat) localVars
                        d localVars' expr)
            Set.unionMany (s1::s2)
        | Ast.DoWhileLoopExp {condition=(_, condition); body=(_, body)} ->
            Set.union (d' condition) (d' body)
        | Ast.FalseExp _ ->
            Set.empty
        | Ast.FloatExp _ ->
            Set.empty
        | Ast.DoubleExp _ ->
            Set.empty
        | Ast.ForInLoopExp {varName=(_, varName); start=(_, start); end_=(_, end_); body=(_, body)} ->
            let s1 = d' start
            let s2 = d' end_
            let s3 = d (Set.add varName localVars) body
            Set.unionMany [s1; s2; s3]
        | Ast.ForLoopExp { initLoop = (_, (Ast.LetExp {left=(_, left)} as initLoop)); loopCondition=(_, loopCondition); loopStep=(_, loopStep); body=(_, body)} ->
            let s1 = d' initLoop
            let localVars' = Set.union localVars (getVars left)
            let s2 = d localVars' loopCondition
            let s3 = d localVars' loopStep
            let s4 = d localVars' body
            Set.unionMany [s1; s2; s3; s4]
        | Ast.ForLoopExp { initLoop = (_, (Ast.VarExp (_, varName) as initLoop)); loopCondition=(_, loopCondition); loopStep=(_, loopStep); body=(_, body)} ->
            let s1 = d' initLoop
            let localVars' = Set.add varName localVars
            let s2 = d localVars' loopCondition
            let s3 = d localVars' loopStep
            let s4 = d localVars' body
            Set.unionMany [s1; s2; s3; s4]
        | Ast.ForLoopExp { initLoop = (_, initLoop); loopCondition=(_, loopCondition); loopStep=(_, loopStep); body=(_, body) } ->
            let s1 = d' initLoop
            let s2 = d' loopCondition
            let s3 = d' loopStep
            let s4 = d' body
            Set.unionMany [s1; s2; s3; s4]
        | Ast.IfElseExp {condition=(_, condition); trueBranch=(_, trueBranch); falseBranch=(_, falseBranch)} ->
            [condition; trueBranch; falseBranch] |> List.map d' |> Set.unionMany
        | Ast.InlineCode _ ->
            Set.empty
        | (Ast.IntExp _ | Ast.Int8Exp _ | Ast.UInt8Exp _ | Ast.Int16Exp _ | Ast.UInt16Exp _ |
            Ast.UInt32Exp _ | Ast.Int32Exp _ | Ast.UInt64Exp _ | Ast.Int64Exp _) ->
            Set.empty
        | Ast.LambdaExp (_, {arguments=(_, arguments); body=(_, body)}) ->
            let argNames = arguments |> List.map (fst >> Ast.unwrap) |> Set.ofList
            d (Set.union argNames localVars) body
        | Ast.LetExp {right=(_, right)} ->
            d' right
        | Ast.ModQualifierExp (_, {module_=(_, module_); name=(_, name)}) ->
            let modqual = (module_, name)
            if Set.contains modqual valueDecs then
                Set.singleton modqual
            else
                Set.empty
        | Ast.Smartpointer ((_, rawptr), (_, destructor)) ->
            Set.union (d' rawptr) (d' destructor)
        | Ast.SizeofExp _ ->
            Set.empty
        | Ast.QuitExp _ ->
            Set.empty
        | Ast.RecordAccessExp {record=(_, record)} ->
            d' record
        | Ast.RefRecordAccessExp {recordRef=(_, recordRef)} ->
            d' recordRef
        | Ast.RecordExp {initFields=(_, initFields)} ->
            initFields |> List.map (snd >> Ast.unwrap >> d') |> Set.unionMany
        | Ast.RefExp (_, expr) ->
            d' expr
        | Ast.SequenceExp (pose, exprs) ->
            let (pos, exp)::rest = exprs
            let localVars' =
                Set.union
                    localVars
                    (match exp with
                    | Ast.LetExp {left=(_, left)} ->
                        getVars left
                    | _ ->
                        Set.empty)
            let s1 = d' exp
            let s2 =
                if List.isEmpty rest then
                    Set.empty
                else
                    d localVars' (Ast.SequenceExp (pose, rest))
            Set.union s1 s2
        | Ast.CharListLiteral _ ->
            Set.empty
        | Ast.StringLiteral _ ->
            Set.empty
        | Ast.TrueExp _ ->
            Set.empty
        | Ast.TupleExp exprs ->
            exprs |> List.map (Ast.unwrap >> d') |> Set.unionMany
        | Ast.TypeConstraint {exp=(_, exp)} ->
            d' exp
        | Ast.UnaryOpExp {exp=(_, exp)} ->
            d' exp
        | Ast.UnitExp _ ->
            Set.empty
        | Ast.VarExp (posv, varName) ->
            if Set.contains varName localVars then
                Set.empty
            else
                match Map.tryFind varName menv with
                | Some modqual when Set.contains modqual valueDecs ->
                    Set.singleton modqual
                | _ ->
                    Set.empty
        | Ast.WhileLoopExp {condition=(_, condition); body=(_, body)} ->
            Set.union (d' condition) (d' body)
        | Ast.IfExp {condition=(_, condition); trueBranch=(_, trueBranch)} ->
            Set.union (d' condition) (d' trueBranch)
        | Ast.DeclVarExp _ ->
            Set.empty
        | Ast.NullExp _ ->
            Set.empty
    d localVars e

let rec findFreeVars (theta : Constraint.ThetaT) (kappa : Constraint.KappaT) (e : T.TyAdorn<T.Expr>) : (Ast.PosAdorn<T.TyVar> list) * (Ast.PosAdorn<T.CapVar> list) =
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

    let freeVarsTemplateApply pos (args : T.TemplateApply) =
        let (tyExprs, capExprs) = Choice.splitChoice2 args
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
        | T.RefMutation exp ->
            ffv exp
        | T.RefRecordMutation {recordRef=recordRef} ->
            ffv recordRef

    let rec freeVarsPattern ((pos, _, pat) : T.TyAdorn<T.Pattern>) =
        match pat with
        | T.MatchVar {typ=typ} ->
            freeVarsTyp pos typ
        | (T.MatchIntVal _ | T.MatchFloatVal _ | T.MatchUnit | T.MatchTrue | T.MatchFalse | T.MatchUnderscore) ->
            ([], [])
        | T.MatchValCon {innerPattern=innerPattern} ->
            append2 (List.map freeVarsPattern innerPattern |> List.unzip)
        | T.MatchRecCon fields ->
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
        | T.DoWhileLoopExp {condition=condition; body=body} ->
            append2 ([ffv condition; ffv body] |> List.unzip)
        | T.Smartpointer (rawPtr, destructor) ->
            append2 ([ffv rawPtr; ffv destructor] |> List.unzip)
        | (T.FalseExp | T.FloatExp _ | T.InlineCode _ | T.IntExp _ |
            T.InternalDeclareVar _ | T.ModQualifierExp _ |
            T.TrueExp | T.UnitExp | T.VarExp _ | T.DoubleExp _ |
            T.Int16Exp _  | T.UInt16Exp _ | T.Int32Exp _ | T.UInt32Exp _ |
            T.UInt64Exp _ | T.Int64Exp _ | T.Int8Exp _ | T.UInt8Exp _ |
            T.InternalUsing _ | T.InternalUsingCap _ | T.NullExp | T.StringExp _) ->
            ([], [])
        | T.ForInLoopExp {typ=typ; start=start; end_=end_; body=body} ->
            append2 ([freeVarsTyp (T.getPos e) typ; ffv start; ffv end_; ffv body] |> List.unzip)
        | T.ForLoopExp {loopCondition=loopCondition; loopStep=loopStep; body=body} ->
            append2 ([ffv loopCondition; ffv loopStep; ffv body] |> List.unzip)
        | T.IfExp {condition=condition; trueBranch=trueBranch} ->
            append2 ([ffv condition; ffv trueBranch] |> List.unzip)
        | T.IfElseExp {condition=condition; trueBranch=trueBranch; falseBranch=falseBranch} ->
            append2 (List.map ffv [condition; trueBranch; falseBranch] |> List.unzip)
        | T.LambdaExp {returnTy=returnTy; arguments=arguments; body=body} ->
            let a = append2 (List.map (snd >> freeVarsTyp (T.getPos e)) arguments |> List.unzip)
            append2 ([freeVarsTyp (T.getPos e) returnTy; a; ffv body] |> List.unzip)
        | T.LetExp {left=left; right=right} ->
            append2 ([freeVarsPattern left; ffv right] |> List.unzip)
        | T.QuitExp typ ->
            freeVarsTyp (T.getPos e) typ
        | T.SizeofExp typ ->
            freeVarsTyp (T.getPos e) typ
        | T.RecordAccessExp {record=record} ->
            ffv record
        | T.RefRecordAccessExp {recordRef=recordRef} ->
            ffv recordRef
        | T.RecordExp {initFields=initFields} ->
            append2 (List.map (snd >> ffv) initFields |> List.unzip)
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
        | T.DeclVarExp {varName=varName; typ=typ} ->
            freeVarsTyp (T.getPos e) typ
        | T.FunctionWrapperEmptyClosure func ->
            ffv func
    
    (List.append freeTaus freeTaus', List.append freeCaps freeCaps')

// Finds variables referenced within expr that are not declared within expr
let closure (expr : T.TyAdorn<T.Expr>) : Set<string> =
    T.preorderFold
        (fun gamma accum expr' ->
            match T.unwrap expr' with
            | T.VarExp name ->
                if Map.containsKey name gamma then
                    accum
                else
                    Set.add name accum
            | _ ->
                accum)
        (fun gamma accum leftAssign' ->
            match leftAssign' with
            | T.VarMutation name ->
                if Map.containsKey name gamma then
                    accum
                else
                    Set.add name accum
            | _ ->
                accum)
        (fun _ accum _ -> accum)
        Map.empty
        Set.empty
        expr