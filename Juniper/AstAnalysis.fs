module AstAnalysis
module A = Ast
module T = TypedAst

// Find all types that a type declaration is referring to
let tyRefs (menv : Map<string, string*string>) tyDec =
    let rec refsInTyExpr t =
        match t with
        | A.BaseTy _ ->
            Set.empty
        | A.ModuleQualifierTy {module_=(_, module_); name=(_, name)} ->
            Set.singleton (module_, name)
        | A.ApplyTy {tyConstructor=(_, tyConstructor); args=(_, {tyExprs=(_, tyExprs)})} ->
            let t1 = refsInTyExpr tyConstructor
            let t2 = List.map (A.unwrap >> refsInTyExpr) tyExprs
            Set.unionMany (t1::t2)
        | A.ArrayTy {valueType=(_, valueType)} ->
            refsInTyExpr valueType
        | A.FunTy {args=args; returnType=(_, returnType)} ->
            let t1 = List.map (A.unwrap >> refsInTyExpr) args
            let t2 = refsInTyExpr returnType
            Set.unionMany (t2::t1)
        | A.NameTy (_, name) ->
            match Map.tryFind name menv with
            | None ->
                Set.empty
            | Some modQual ->
                Set.singleton modQual
        | A.ParensTy (_, tau) ->
            refsInTyExpr tau
        | A.RefTy (_, tau) ->
            refsInTyExpr tau
        | A.TupleTy taus ->
            taus |> List.map (A.unwrap >> refsInTyExpr) |> Set.unionMany
        | A.VarTy _ ->
            Set.empty

    match tyDec with
    | A.UnionDec {valCons=(_, valCons)} ->
        valCons |>
        List.map
            (fun valueCon ->
                match valueCon with
                | (_, Some (_, tyExpr)) -> refsInTyExpr tyExpr
                | _ -> Set.empty) |>
        Set.unionMany
    | A.RecordDec {fields=(_, fields)} ->
        fields |>
        List.map (snd >> A.unwrap >> refsInTyExpr) |>
        Set.unionMany
    

// Find all top level function and let declarations (value declarations)
// that some expression is referring to
let decRefs valueDecs (menv : Map<string, string*string>) localVars e =
    let rec getVars pattern =
        match pattern with
        | (Ast.MatchFalse _ | Ast.MatchFloatVal _ | Ast.MatchIntVal _ | Ast.MatchTrue _ |
            Ast.MatchUnderscore _ | Ast.MatchUnit _) ->
            Set.empty
        | Ast.MatchRecCon {fields=(_, fields)} ->
            Set.unionMany (List.map (snd >> Ast.unwrap >> getVars) fields)
        | Ast.MatchTuple (_, elements) ->
            Set.unionMany (List.map (Ast.unwrap >> getVars) elements)
        | Ast.MatchValCon {name=(_, name); innerPattern=innerPattern} ->
            innerPattern |> Option.map (Ast.unwrap >> getVars) |> Option.toList |> Set.unionMany
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
        | Ast.VarMutation (_, name) ->
            match Map.tryFind name menv with
            | Some modqual when Set.contains modqual valueDecs ->
                Set.singleton modqual
            | _ -> Set.empty

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
        | Ast.ForLoopExp {varName=(_, varName); start=(_, start); end_=(_, end_); body=(_, body)} ->
            let s1 = d' start
            let s2 = d' end_
            let s3 = d (Set.add varName localVars) body
            Set.unionMany [s1; s2; s3]
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
        | Ast.Smartpointer ((_, varname), (_, body)) ->
            d (Set.add varname localVars) body
        | Ast.QuitExp _ ->
            Set.empty
        | Ast.RecordAccessExp {record=(_, record)} ->
            d' record
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
        | Ast.TemplateApplyExp {func=(posf, func)} ->
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
        | Ast.UnsafeTypeCast {exp=(_, exp)} ->
            d' exp
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
    d localVars e

let rec findFreeVars (theta : Map<string, T.TyExpr>) (kappa : Map<string, T.CapacityExpr>) (e : T.TyAdorn<T.Expr>) : (Ast.PosAdorn<string> list) * (Ast.PosAdorn<string> list) =
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
        | T.DoWhileLoopExp {condition=condition; body=body} ->
            append2 ([ffv condition; ffv body] |> List.unzip)
        | T.Smartpointer (_, expr) ->
            ffv expr
        | (T.FalseExp | T.FloatExp _ | T.InlineCode _ | T.IntExp _ |
            T.InternalDeclareVar _ | T.ModQualifierExp _ |
            T.TrueExp | T.UnitExp | T.VarExp _ | T.DoubleExp _ |
            T.Int16Exp _  | T.UInt16Exp _ | T.Int32Exp _ | T.UInt32Exp _ |
            T.UInt64Exp _ | T.Int64Exp _ | T.Int8Exp _ | T.UInt8Exp _) ->
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