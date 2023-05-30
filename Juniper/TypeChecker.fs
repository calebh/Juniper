module TypeChecker
module A = Ast
module T = TypedAst
open Constraint
open Extensions
open QuikGraph.Algorithms
open ConvertAst
open Error
open AstAnalysis
open Module
open TypedAst
open System.Threading

let rec typeof ((posE, e) : Ast.PosAdorn<Ast.Expr>)
               (denv : Map<string * string, A.PosAdorn<A.Declaration>>)
               (dtenv : Map<string * string, T.DeclarationTy>)
               (menv : Map<string, string*string>)
               (localVars : Set<string>)
               (ienv : Map<string * string, int>)
               (tyVarMapping : Map<string, T.TyExpr>)
               (capVarMapping : Map<string, T.CapacityExpr>)
               // First bool represents mutability
               (gamma : Map<string, bool * T.TyScheme>) =
    let getTypes = List.map T.getType

    let convertType' = convertType menv denv dtenv tyVarMapping capVarMapping
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
            | Ast.MatchTuple (_, pats) ->
                let innerTaus = List.map freshtyvar pats
                let c = tuplety innerTaus =~= (tau, errStr [posp] "Tuple pattern does not match the expression.")
                let (pats', c') = checkPatterns (List.zip pats innerTaus)
                ((posp, tau, T.MatchTuple pats'), c &&& c')
            | Ast.MatchFalse _ ->
                ((posp, tau, T.MatchFalse), T.booltype =~= (tau, errStr [posp] "False pattern does not match the type of the expression."))
            | Ast.MatchTrue _ ->
                ((posp, tau, T.MatchTrue), T.booltype =~= (tau, errStr [posp] "True pattern does not match the type of the expression."))
            | Ast.MatchFloatVal (_, value) ->
                ((posp, tau, T.MatchFloatVal value), InterfaceConstraint (tau, IsReal, errStr [posp] "Float pattern must satisfy the interface real constraint. Are you sure that you're matching on a real number (float or double)?"))
            | Ast.MatchIntVal (_, value) ->
                ((posp, tau, T.MatchIntVal value), InterfaceConstraint (tau, IsNum, errStr [posp] "Integer pattern must satisfy the interface num constraint. Are you sure that you're matching on a number?"))
            | Ast.MatchUnderscore _ ->
                ((posp, tau, T.MatchUnderscore), Trivial)
            | Ast.MatchUnit (posu, _) ->
                ((posp, tau, T.MatchUnit), T.unittype =~= (tau, errStr [posu] "Unit pattern does not match the type of the expression."))
            | Ast.MatchVar { varName=(posv, varName); mutable_=(posm, mutable_); typ=typ } ->
                if Set.contains varName localVars then
                    raise <| TypeError ((errStr [posv] (sprintf "This pattern already contains a variable named %s." varName)).Force())
                else
                    localVars <- Set.add varName localVars
                    let (c', retTau) =
                        match typ with
                        | Some typ ->
                            let typ' = convertType' typ
                            gamma' <- Map.add varName (mutable_, T.Forall (emptytemplate, [], typ')) gamma'
                            (tau =~= (typ', errStr [A.getPos typ] "Type constraint in pattern could not be satisfied"), typ')
                        | None ->
                            // NOTICE THAT WE DO NOT GENERALIZE HERE
                            // This is what makes this type system different from
                            // Hindley Milner
                            gamma' <- Map.add varName (mutable_, T.Forall (emptytemplate, [], tau)) gamma'
                            (Trivial, tau)
                    ((posp, retTau, T.MatchVar { varName=varName; mutable_=mutable_; typ=tau}), c')
            | Ast.MatchRecCon (posf, fields) ->
                let fieldTaus = List.map freshtyvar fields
                let fieldConstraints =
                    List.zip fieldTaus fields |>
                    List.map
                        (fun (fieldTau, ((posn, name), _)) ->
                            InterfaceConstraint (tau, HasField (name, fieldTau), errStr [posn] (sprintf "Expected type to have a field named %s" name))) |>
                    conjoinConstraints
                let (pats', c) = checkPatterns (List.zip (List.map snd fields) fieldTaus)
                ((posp, tau, T.MatchRecCon (List.zip (List.map (fst >> A.unwrap) fields) pats')), fieldConstraints &&& c)
            | Ast.MatchValCon {name=(posn, decref); innerPattern=(posi, innerPattern)} ->
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
                        {T.ModQualifierRec.module_=Ast.unwrap mod_; T.ModQualifierRec.name=Ast.unwrap name}
                let {T.ModQualifierRec.module_=module_; T.ModQualifierRec.name=name} = modQual
                // Lookup a value constructor in dtenv
                match Map.tryFind (module_, name) dtenv with
                | Some (T.FunDecTy valueConstructor) ->
                    let id = Map.find (module_, name) ienv
                    // Value constructors do not currently allow interface constraints, so just ignore that field
                    let (inst, _, _) = freshInstance valueConstructor
                    match inst with
                    | T.ConApp (T.FunTy, _::(Choice1Of2 returnTau)::wrappedArgTaus) ->
                        let argTaus = List.map (fun (Choice1Of2 argTau) -> argTau) wrappedArgTaus
                        if List.length argTaus = List.length innerPattern then
                            let c = returnTau =~= (tau, errStr [posn] "Value constructor pattern type does not match the expression.")
                            let (innerPattern'', cs) =
                                List.zip argTaus innerPattern |>
                                List.map
                                    (fun (valueConTau, innerPattern') ->
                                        checkPattern' innerPattern' valueConTau) |>
                                List.unzip
                            let c' = c &&& (conjoinConstraints cs)
                            ((posp, tau, T.MatchValCon {modQualifier=modQual; innerPattern=innerPattern''; id = id}), c')
                        else
                            raise <| TypeError ((errStr [posi] (sprintf "Value constructor named %s takes %d arguments, but there were %d inner patterns." name (List.length argTaus) (List.length innerPattern))).Force())
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
            let (tau, c) = typeof e denv dtenv menv localVars ienv tyVarMapping capVarMapping gamma
            let (taus, c') = typesof es dtenv menv localVars gamma
            (tau::taus, c &&& c')
    and ty ((posE, expr) : Ast.PosAdorn<Ast.Expr>) : (T.TyAdorn<T.Expr> * Constraint) =
        let adorn pos tau expr con =
            ((pos, tau, expr), con)
        match expr with
        | Ast.UnitExp (pos, ()) ->
            adorn posE T.unittype T.UnitExp Trivial
        | Ast.InlineCode (pos, code) ->
            adorn posE T.unittype (T.InlineCode code) Trivial
        | Ast.TrueExp (pos, ()) ->
            adorn posE T.booltype T.TrueExp Trivial
        | Ast.FalseExp (pos, ()) ->
            adorn posE T.booltype T.FalseExp Trivial
        | Ast.IntExp (pos, num) ->
            let tyVar = freshtyvar ()
            adorn posE tyVar (T.IntExp num) (InterfaceConstraint (tyVar, IsNum, errStr [pos] "Polymorphic integer literal must be constrained to a numeric type"))
        | Ast.Int8Exp (pos, num) ->
            adorn posE T.int8type (T.Int8Exp num) Trivial
        | Ast.Int16Exp (pos, num) ->
            adorn posE T.int16type (T.Int16Exp num) Trivial
        | Ast.Int32Exp (pos, num) ->
            adorn posE T.int32type (T.Int32Exp num) Trivial
        | Ast.Int64Exp (pos, num) ->
            adorn posE T.int64type (T.Int64Exp num) Trivial
        | Ast.UInt8Exp (pos, num) ->
            adorn posE T.uint8type (T.UInt8Exp num) Trivial
        | Ast.UInt16Exp (pos, num) ->
            adorn posE T.uint16type (T.UInt16Exp num) Trivial
        | Ast.UInt32Exp (pos, num) ->
            adorn posE T.uint32type (T.UInt32Exp num) Trivial
        | Ast.UInt64Exp (pos, num) ->
            adorn posE T.uint64type (T.UInt64Exp num) Trivial
        | Ast.FloatExp (pos, num) ->
            adorn posE T.floattype (T.FloatExp num) Trivial
        | Ast.DoubleExp (pos, num) ->
            adorn posE T.doubletype (T.DoubleExp num) Trivial
        | Ast.SizeofExp tyExpr ->
            let tyExpr' = convertType' tyExpr
            adorn posE T.uint32type (T.SizeofExp tyExpr') Trivial
        | Ast.IfExp {condition = (posc, _) as condition; trueBranch=(post, _) as trueBranch} ->
            let (exprs', c) = typesof [condition; trueBranch] dtenv menv localVars gamma
            let [condition'; trueBranch'] = exprs'
            let [tauC; tauT] = getTypes exprs'
            let c' = c &&& (tauC =~= (T.booltype, errStr [posc] "Condition of if statement expected to be type bool"))
            adorn posE T.unittype (T.IfExp {condition=condition'; trueBranch=trueBranch'}) c'
        | Ast.IfElseExp {condition=(posc, _) as condition; trueBranch=(post, _) as trueBranch; falseBranch=(posf, _) as falseBranch} ->
            let (exprs', c) = typesof [condition; trueBranch; falseBranch] dtenv menv localVars gamma
            let [condition'; trueBranch'; falseBranch'] = exprs'
            let [tauC; tauT; tauF] = getTypes exprs'
            let c' = c &&&
                        (tauC =~= (T.booltype, errStr [posc] "Condition of if statement expected to be type bool")) &&&
                        (tauT =~= (tauF, errStr [post; posf] "Branches of if statement expected to be of the same type"))
            adorn posE tauT (T.IfElseExp {condition=condition'; trueBranch=trueBranch'; falseBranch=falseBranch'}) c'
        | Ast.VarExp (posn, varName) ->
            match Map.tryFind varName gamma with
            | Some (_, tyscheme) ->
                let (instance, interfaceConstraints, freshVars) = freshInstance tyscheme
                let err = errStr [posn] "The interface constraints are not satisfied."
                let interfaceConstraints' = interfaceConstraints |> List.map (fun (conTau, con) -> InterfaceConstraint (conTau, con, err)) |> conjoinConstraints
                let expr' =
                    match freshVars with
                    | [] -> T.VarExp varName
                    | _ -> T.TemplateApplyExp {func=Choice1Of2 varName; templateArgs=freshVars}
                let expr'' =
                    if Set.contains varName localVars then
                        expr'
                    else
                        match Map.find (Map.find varName menv) dtenv with
                        | FunDecTy _ ->
                            T.FunctionWrapperEmptyClosure (posE, instance, expr')
                        | _ ->
                            expr'
                adorn posE instance expr'' interfaceConstraints'
            | None ->
                raise <| TypeError ((errStr [posn] (sprintf "Variable named %s could not be found" varName)).Force())
        | Ast.ArrayAccessExp { array=(posa, _) as array; index=(posi, _) as index } ->
            let (exprs', c) = typesof [array; index] dtenv menv localVars gamma
            let [array'; index'] = exprs'
            let [tauA; tauI] = getTypes exprs'
            let tauElement = freshtyvar ()
            let arraySize = freshcapvar ()
            let tauArray = T.ConApp (T.ArrayTy, [Choice1Of2 tauElement; Choice2Of2 arraySize])
            let c' = c &&& (tauA =~= (tauArray, errStr [posa] "An array access expression must access a value of an array type")) &&&
                           (InterfaceConstraint (tauI, IsInt, errStr [posi] "Expected index of array access expression to have integer type"))
            adorn posE tauElement (T.ArrayAccessExp {array=array'; index=index'}) c'
        | Ast.ArrayLitExp (posa, exprs) ->
            let (exprs', c) = typesof exprs dtenv menv localVars gamma
            let tauElement = freshtyvar ()
            let c' = List.fold (&&&) c (List.map (flip (T.getType >> (=~=)) (tauElement, errStr [posa] "Expected all elements of array to be of the same type")) exprs')
            let tauArray = T.ConApp (T.ArrayTy, [Choice1Of2 tauElement; Choice2Of2 (T.CapacityConst (int64 (List.length exprs)))])
            adorn posE tauArray (T.ArrayLitExp exprs') c'
        | Ast.ArrayMakeExp {typ=typ; initializer=maybeInitializer} ->
            let post = A.getPos typ
            let typ' = convertType' typ
            match typ' with
            | T.ConApp (T.ArrayTy, [Choice1Of2 tauElement; Choice2Of2 cap]) ->
                let (maybeInitializer', c) =
                    match maybeInitializer with
                    | Some ((posi, _) as initializer) ->
                        let (initializer', c) = ty initializer
                        let c' = c &&& (T.getType initializer' =~= (tauElement, errStr [post; posi] "Expected initializer to have the same type as the type declaration."))
                        (Some initializer', c')
                    | None ->
                        (None, Trivial)
                adorn posE typ' (T.ArrayMakeExp {typ=typ'; initializer=maybeInitializer'}) c
            | _ ->
                raise <| TypeError ((errStr [post] "Type declaration should be an array type").Force())
        | Ast.AssignExp {left=(posl, left); right=(posr, _) as right; } ->
            let rec checkLeft left =
                let ((_, retTau, left'), c) =
                    match left with
                    | Ast.ModQualifierMutation (posmq, {module_=(posm, module_); name=(posn, name)}) ->                    
                        match Map.tryFind (module_, name) dtenv with
                        | Some (T.LetDecTy tau) ->
                            // TODO: Update this if we decide to make module level values mutable
                            //adorn posl tau (T.ModQualifierMutation {module_=module_; name=name}) Trivial
                            raise <| TypeError ((errStr [posmq] "Top level let declarations are not mutable. Did you mean to use a derefence set (ie *x = ...) instead?").Force())
                        | Some _ ->
                            raise <| TypeError ((errStr [posn] (sprintf "Found a declaration named %s in module %s, but it was not a let declaration." name module_)).Force())
                        | None ->
                            raise <| TypeError ((errStr [posmq] (sprintf "Unable to find a let declaration named %s in module %s." name module_)).Force())
                    | Ast.ArrayMutation {array=(posa, array); index=(posi, _) as index} ->
                        let elementTau = freshtyvar ()
                        let capVar = freshcapvar ()
                        let (array', c1) = checkLeft array
                        let (index', c2) = ty index
                        let c' = c1 &&& c2 &&& (InterfaceConstraint (T.getType index', IsInt, errStr [posi] "Array index must be an integer type.")) &&&
                                               ((T.getType array') =~= (T.ConApp (T.ArrayTy, [Choice1Of2 elementTau; Choice2Of2 capVar]), errStr [posa] "Expected an array type to perform an array mutation upon"))
                        adorn posl elementTau (T.ArrayMutation {array=T.unwrap array'; index=index'}) c'
                    | Ast.RecordMutation {record=(posr, record); fieldName=(posf, fieldName)} ->
                        let (record', c) = checkLeft record
                        let fieldTau = freshtyvar ()
                        let c' = c &&& InterfaceConstraint (T.getType record', HasField (fieldName, fieldTau), errStr [posE] (sprintf "Expected the expression to be a record type and have a field named %s" fieldName))
                        adorn posl fieldTau (T.RecordMutation {record=T.unwrap record'; fieldName=fieldName}) c'
                    | Ast.RefRecordMutation {recordRef=(posr, _) as recordRef; fieldName=(posf, fieldName)} ->
                        let (recordRef', c) = ty recordRef
                        let recordTau = freshtyvar ()
                        let refConstraint = (T.ConApp (T.RefTy, [Choice1Of2 recordTau])) =~= (T.getType recordRef', errStr [posr] "Left hand side of ref record access must be a ref")
                        let fieldTau = freshtyvar ()
                        let fieldConstraint = InterfaceConstraint (recordTau, HasField (fieldName, fieldTau), errStr [posE] (sprintf "Expected the expression to be a record ref type and have a field named %s" fieldName))
                        let c' = c &&& refConstraint &&& fieldConstraint
                        adorn posl fieldTau (T.RefRecordMutation {recordRef=recordRef'; fieldName=fieldName}) c'
                    | Ast.VarMutation (posn, name) ->
                        match Map.tryFind name gamma with
                        | Some (isMutable, tyscheme) ->
                            if isMutable then
                                let (tau, interfaceConstraints, _) = freshInstance tyscheme
                                let err = errStr [posn] "The interface constraints are not satisfied."
                                let interfaceConstraints' = interfaceConstraints |> List.map (fun (conTau, con) -> InterfaceConstraint (conTau, con, err)) |> conjoinConstraints
                                adorn posl tau (T.VarMutation name) interfaceConstraints'
                            else
                                raise <| TypeError ((errStr [posn] (sprintf "The variable named %s is not mutable." name)).Force())
                        | None ->
                            raise <| TypeError ((errStr [posn] (sprintf "Unable to find variable named %s in the current scope." name)).Force())
                    | Ast.RefMutation ((pose, _) as expr) ->
                        let (expr', c) = ty expr
                        let tau = freshtyvar ()
                        let c' = c &&& (T.getType expr' =~= (T.ConApp (T.RefTy, [Choice1Of2 tau]), errStr [pose] "The left hand side of the assignment operation is not a reference, but a dereference operation (*) was used. Are you sure you meant to set a ref cell?"))
                        adorn posl tau (T.RefMutation expr') c'
                adorn posl retTau left' c
            // End checkleft
            let (right', c1) = ty right
            let (left', c2) = checkLeft left
            let c' = c1 &&& c2 &&& (T.getType left' =~= (T.getType right', (errStr [posl; posr] "The type of the left hand side should match the type of the right hand side in a set expression.")))
            adorn posE (T.getType right') (T.AssignExp {left=left'; right=right'}) c'
        | Ast.BinaryOpExp {left=(posl, _) as left; op=(poso, A.Pipe); right=(posr, _) as right} ->
            match A.unwrap right with
            | A.CallExp {func=func; args=(posa, args)} ->
                ty (posr, A.CallExp {func=func; args=(posa, args @ [left])})
            | _ ->
                raise <| TypeError ((errStr [posr] "The right hand side of the pipe operator must be a function call expression").Force())
        | Ast.BinaryOpExp {left=(posl, _) as left; op=(poso, op); right=(posr, _) as right} ->
            let op' =
                match op with
                | Ast.Add -> T.Add
                | Ast.BitshiftLeft -> T.BitshiftLeft
                | Ast.BitshiftRight -> T.BitshiftRight
                | Ast.BitwiseAnd -> T.BitwiseAnd
                | Ast.BitwiseOr -> T.BitwiseOr
                | Ast.BitwiseXor -> T.BitwiseXor
                | Ast.Divide -> T.Divide
                | Ast.Equal -> T.Equal
                | Ast.Greater -> T.Greater
                | Ast.GreaterOrEqual -> T.GreaterOrEqual
                | Ast.Less -> T.Less
                | Ast.LessOrEqual -> T.LessOrEqual
                | Ast.LogicalAnd -> T.LogicalAnd
                | Ast.LogicalOr -> T.LogicalOr
                | Ast.Modulo -> T.Modulo
                | Ast.Multiply -> T.Multiply
                | Ast.NotEqual -> T.NotEqual
                | Ast.Subtract -> T.Subtract
            let (left', c1) = ty left
            let (right', c2) = ty right
            let c' = c1 &&& c2
            let b' = T.BinaryOpExp {left=left'; op=op'; right=right'}
            match op with
            | (Ast.LogicalAnd | Ast.LogicalOr) ->
                let c'' = c' &&& (T.booltype =~= (T.getType left', errStr [posl] "Left hand side of binary expression should be of type boolean")) &&&
                                 (T.booltype =~= (T.getType right', errStr [posr] "Right hand side of binary expression should be of type boolean"))
                adorn posE T.booltype b' c''
            | (Ast.Equal | Ast.NotEqual) ->
                let c'' = c' &&& (T.getType left' =~= (T.getType right', errStr [posl; posr] "Left hand side and right hand side of binary expression should be the same type"))
                adorn posE T.booltype b' c''
            | (Ast.Greater | Ast.GreaterOrEqual | Ast.Less | Ast.LessOrEqual) ->
                let cLeft = InterfaceConstraint (T.getType left', IsNum, errStr [posl] "The left hand side must be a number type")
                let cRight = InterfaceConstraint (T.getType right', IsNum, errStr [posr] "The right hand side must be a number type")
                let c'' = c' &&& cLeft &&& cRight
                adorn posE T.booltype b' c''
            | (Ast.BitshiftLeft | Ast.BitshiftRight) ->
                let cLeft = InterfaceConstraint (T.getType left', IsInt, errStr [posl] "The left hand side of this bitshift operation must be an integer.")
                let cRight = InterfaceConstraint (T.getType right', IsInt, errStr [posr] "The right hand side of this bitshift operation must be an integer.")
                let c'' = c' &&& cLeft &&& cRight
                adorn posE (T.getType left') b' c''
            | (Ast.BitwiseAnd | Ast.BitwiseOr | Ast.BitwiseXor) ->
                let cLeft = InterfaceConstraint (T.getType left', IsInt, errStr [posl] "The left hand side of this bitwise operation must be an integer.")
                let cRight = InterfaceConstraint (T.getType right', IsInt, errStr [posr] "The right hand side of this bitwise operation must be an integer.")
                let cEq = ((T.getType left') =~= (T.getType right', errStr [posl; posr] "Left and right hand must be of the same type for this operation"))
                let c'' = c' &&& cLeft &&& cRight &&& cEq
                adorn posE (T.getType left') b' c''
            | (Ast.Add | Ast.Divide | Ast.Modulo | Ast.Multiply | Ast.Subtract) ->
                let cLeft = InterfaceConstraint (T.getType left', IsNum, errStr [posl] "The left hand side must be a number type")
                let cRight = InterfaceConstraint (T.getType right', IsNum, errStr [posr] "The right hand side must be a number type")
                let cEq = ((T.getType left') =~= (T.getType right', errStr [posl; posr] "Left and right hand must be of the same type for this operation"))
                let c'' = c' &&& cLeft &&& cRight &&& cEq
                adorn posE (T.getType left') b' c''
        | Ast.CallExp {func=(posf, _) as func; args=(posa, args)} ->
            let (func', c1) = ty func
            let (args', c2) = typesof args dtenv menv localVars gamma
            let closureTau = freshtyvar ()
            let returnTau = freshtyvar ()
            let placeholders = List.map freshtyvar args
            let c3 = funty closureTau returnTau placeholders =~= (T.getType func', errStr [posf; posa] "The function being called does not have a function type or the number of parameters passed to the function is incorrect.")
            let c4 =
                List.map
                    (fun ((posa, _), arg', placeholder) ->
                        placeholder =~= (T.getType arg', errStr [posa] "The type of the argument is incorrect."))
                    (List.zip3 args args' placeholders)
            let c' = c1 &&& c2 &&& c3 &&& (List.fold (&&&) Trivial c4)
            adorn posE returnTau (T.CallExp {func=func'; args=args'}) c'
        | Ast.CaseExp {on=(poso, _) as on; clauses=(posc, clauses)} ->
            let (on', c1) = ty on
            let (clauses', c2) =
                List.map
                    (fun (pattern, ((pose, _) as expr)) ->
                        let (pattern', c1, localVars1, gamma') = checkPattern pattern (T.getType on')
                        let localVars' = Set.union localVars localVars1
                        let (expr', c2) = typeof expr denv dtenv menv localVars' ienv tyVarMapping capVarMapping gamma'
                        let c' = c1 &&& c2
                        ((pattern', expr'), c'))
                    clauses |>
                List.unzip
            match (List.map (snd >> Ast.getPos) clauses, List.map (snd >> T.getType) clauses') with
            | (firstClausePos::otherClausesPos, firstClauseTau::otherClausesTaus) ->
                let c3 =
                    List.zip otherClausesPos otherClausesTaus |>
                    List.map
                        (fun (pos, clauseTau) ->
                            firstClauseTau =~= (clauseTau, errStr [firstClausePos; pos] "All clauses in case expression should have the same type.")) |>
                    List.fold (&&&) Trivial
                let c' = List.fold (&&&) Trivial ((c1 &&& c3)::c2)
                adorn posE firstClauseTau (T.CaseExp {on=on'; clauses=clauses'}) c'
            | _ ->
                raise <| TypeError ((errStr [posc] "No clauses were found in the case statement").Force())
        | Ast.DoWhileLoopExp {condition=(posc, _) as condition; body=(posb, _) as body} ->
            let (body', c1) = ty body
            let (condition', c2) = ty condition
            let c' = c1 &&& c2 &&& (T.getType condition' =~= (T.booltype, errStr [posc] "Condition of do while loop must be of boolean type"))
            adorn posE T.unittype (T.DoWhileLoopExp {condition=condition'; body=body'}) c'
        | Ast.WhileLoopExp {condition=(posc, _) as condition; body=(posb, _) as body} ->
            let (body', c1) = ty body
            let (condition', c2) = ty condition
            let c' = c1 &&& c2 &&& (T.getType condition' =~= (T.booltype, errStr [posc] "Condition of while loop must be of boolean type"))
            adorn posE T.unittype (T.WhileLoopExp {condition=condition'; body=body'}) c'
        | Ast.ForInLoopExp {typ=maybeTyp; varName=(posv, varName); start=(poss, _) as start; body=(posb, _) as body; end_=(pose, _) as end_} ->
            let tauIterator =
                match maybeTyp with
                | Some tau ->
                    convertType' tau
                | None ->
                    freshtyvar ()
            let (start', c1) = ty start
            let (end_', c2) = ty end_
            let gamma' = Map.add varName (false, T.Forall (emptytemplate, [], tauIterator)) gamma
            let (body', c3) = typeof body denv dtenv menv (Set.add varName localVars) ienv tyVarMapping capVarMapping gamma'
            let c' = c1 &&& c2 &&& c3 &&& (tauIterator =~= (T.getType start', errStr [posv; poss] "Type of the start expression does not match the type of the iterator")) &&&
                                          (tauIterator =~= (T.getType end_', errStr [posv; pose] "Type of the end expression doesn't match the type of the iterator")) &&&
                                          (InterfaceConstraint (tauIterator, IsInt, errStr [posv] "Variable must be of integer type"))
            adorn posE T.unittype (T.ForInLoopExp {typ=tauIterator; varName=varName; start=start'; end_=end_'; body=body'}) c'
        | Ast.ForLoopExp { initLoop=(_, Ast.UnitExp _); loopCondition=(posc, _) as loopCondition; loopStep=loopStep; body=body} ->
            // No initializer needed for this loop (it is a unit expression)
            let (loopCondition', c1) = ty loopCondition
            let (loopStep', c2) = ty loopStep
            let (body', c3) = ty body
            let c' = c1 &&& c2 &&& c3 &&& (T.getType loopCondition' =~= (T.booltype, errStr [posc] "Condition of for loop must be of boolean type"))
            adorn posE T.unittype (T.ForLoopExp {loopCondition=loopCondition'; loopStep=loopStep'; body=body'}) c'
        | Ast.ForLoopExp { initLoop=initLoop; loopCondition=loopCondition; loopStep=loopStep; body=body} ->
            // Move the initializers outside the loop and into their own sequence
            // Initializer becomes a unit expression
            let initPos = Ast.getPos initLoop
            let initUnit = (initPos, Ast.UnitExp (initPos, ()))
            let loop' = (posE, Ast.SequenceExp (posE, [initLoop; (posE, Ast.ForLoopExp { initLoop=initUnit; loopCondition=loopCondition; loopStep=loopStep; body=body })]))
            ty loop'
        | Ast.LambdaExp (posf, {returnTy=maybeReturnTy; arguments=(posargs, arguments); body=(posb, _) as body; interfaceConstraints=(posi, interfaceConstraints)}) ->
            match interfaceConstraints with
            | [] -> ()
            | _ -> raise <| SemanticError ((errStr [posi] "Interface constraints are not supported for lambdas").Force())
            let gamma' = gamma |> Map.map (fun varName (_, scheme) -> (false, scheme)) // Mark all variables as non-mutable within the lambda
            let (gamma1Lst, c1s, localVars1, arguments') =
                arguments |>
                List.map
                    (fun ((posa, argName), maybeArgTau) ->
                        let tau = freshtyvar ()
                        let argConstraint =
                            match maybeArgTau with
                            | Some tauConstraint ->
                                convertType' tauConstraint =~= (tau, errStr [A.getPos tauConstraint] "Invalid argument type constraint")
                            | None ->
                                Trivial
                        let gammaEntry = (argName, (false, T.Forall (emptytemplate, [], tau)))
                        (gammaEntry, argConstraint, argName, (argName, tau))) |>
                List.unzip4
            let gamma'' = Map.merge gamma' (Map.ofList gamma1Lst)
            let c1 = c1s |> conjoinConstraints            
            let localVars' = Set.union localVars (Set.ofList localVars1)
            let (body', c2) = typeof body denv dtenv menv localVars' ienv tyVarMapping capVarMapping gamma''
            let closureVariables = Set.intersect localVars (AstAnalysis.closure body')
            let (closureList, interfaceConstraints) =
                closureVariables |>
                List.ofSeq |>
                List.map
                    (fun closedVarName ->
                        let (_, tyScheme) = Map.find closedVarName gamma
                        let (inst, interfaceConstraints, _) = freshInstance tyScheme
                        ((closedVarName, inst), interfaceConstraints)) |>
                List.unzip
            let closure = Map.ofList closureList
            let err = errStr [posf] "The interface constraints generated by constructing the closure of the lambda could not be satisfied."
            let interfaceConstraints' = interfaceConstraints |> Seq.concat |> Seq.map (fun (conTau, con) -> InterfaceConstraint (conTau, con, err)) |> List.ofSeq |> conjoinConstraints
            let c3 = 
                match maybeReturnTy with
                | Some returnTau ->
                    convertType' returnTau =~= (T.getType body', errStr [A.getPos returnTau] "Invalid return type constraint")
                | None ->
                    Trivial
            let lambdaTau = funty (ClosureTy closure) (T.getType body') (List.map snd arguments')
            let c' = interfaceConstraints' &&& c1 &&& c2 &&& c3
            adorn posE lambdaTau (T.LambdaExp {closure = closure; returnTy=T.getType body'; arguments=arguments'; body=body'}) c'
        // Hit a let expression that is not part of a sequence
        // In this case its variable bindings are useless, but the right hand side might still
        // produce side effects
        // We also have to make sure that the pattern matching agrees with the type of the right
        | Ast.LetExp {left=left; right=(posr, _) as right} ->
            let (right', c1) = ty right
            let (left', c2, _, _) = checkPattern left (T.getType right')
            let c' = c1 &&& c2
            adorn posE (T.getType left') (T.LetExp {left=left'; right=right'}) c'
        | Ast.DeclVarExp {varName=varName; typ=typ} ->
            let typ' = convertType' typ
            adorn posE typ' (T.DeclVarExp {varName=A.unwrap varName; typ=typ'}) Trivial
        | Ast.ModQualifierExp (posmq, {module_=(pos, module_); name=(posn, name)}) ->
            let (instance, interfaceConstraints, templateArgs) =
                match Map.tryFind (module_, name) dtenv with
                | Some (T.FunDecTy tyscheme) ->
                    freshInstance tyscheme
                | Some (T.LetDecTy tau) ->
                    (tau, [], [])
                | Some (T.AliasDecTy _) ->
                    raise <| TypeError ((errStr [posmq] (sprintf "Found declaration named %s in module %s, but it was a alias type declaration and not a value declaration." name module_)).Force())
                | Some (T.UnionDecTy _) ->
                    raise <| TypeError ((errStr [posmq] (sprintf "Found declaration named %s in module %s, but it was an algebraic datatype declaration and not a value declaration." name module_)).Force())
                | None ->
                    raise <| TypeError ((errStr [posmq] (sprintf "Unable to find declaration named %s in module %s." name module_)).Force())
            let expr' =
                match templateArgs with
                | [] -> T.ModQualifierExp {module_=module_; name=name}
                | _ -> T.TemplateApplyExp {func=Choice2Of2 {module_=module_; name=name}; templateArgs=templateArgs}
            let err = errStr [posmq] "The template arguments to the function do not satisfy the interface constraints."
            let interfaceConstraints' = interfaceConstraints |> List.map (fun (conTau, con) -> InterfaceConstraint (conTau, con, err)) |> conjoinConstraints
            adorn posE instance expr' interfaceConstraints'
        | Ast.QuitExp maybeTau ->
            let tau =
                match maybeTau with
                | Some tau ->
                    convertType' tau
                | None ->
                    freshtyvar ()
            adorn posE tau (T.QuitExp tau) Trivial
        | Ast.RecordAccessExp {record=(posr, _) as record; fieldName=(posf, fieldName)} ->
            let (record', c') = ty record
            let tau = freshtyvar ()
            let fieldConstraint = InterfaceConstraint (T.getType record', HasField (fieldName, tau), errStr [posE] (sprintf "Expected the expression to be a record type and have a field named %s" fieldName))
            let c'' = c' &&& fieldConstraint
            adorn posE tau (T.RecordAccessExp {record=record'; fieldName=fieldName}) c''
        | Ast.RefRecordAccessExp {recordRef=(posr, _) as recordRef; fieldName=(posf, fieldName)} ->
            let (recordRef', c') = ty recordRef
            let recordTau = freshtyvar ()
            let refConstraint = (T.ConApp (T.RefTy, [Choice1Of2 recordTau])) =~= (T.getType recordRef', errStr [posr] "Left hand side of ref record access must be a ref")
            let fieldTau = freshtyvar ()
            let fieldConstraint = InterfaceConstraint (recordTau, HasField (fieldName, fieldTau), errStr [posE] (sprintf "Expected the expression to be a record ref type and have a field named %s" fieldName))
            let c'' = c' &&& refConstraint &&& fieldConstraint
            adorn posE fieldTau (T.RefRecordAccessExp {recordRef=recordRef'; fieldName=fieldName}) c''
        | Ast.RecordExp { packed=maybePacked; initFields=(posi, initFields)} ->
            let initFieldNames = initFields |> List.map (fst >> Ast.unwrap)
            let maybePacked' =
                match maybePacked with
                | Some _ -> Some initFieldNames
                | None -> None
            let isPacked = Option.isSome maybePacked
            let (fieldExprs', c') =
                initFields |>
                List.map
                    (fun ((_, fieldName), fieldExpr) ->
                        let (fieldExpr', c) = ty fieldExpr
                        (fieldName, fieldExpr'), c) |>
                List.unzip
            let c'' = conjoinConstraints c'
            let tauFields =
                fieldExprs' |>
                List.map (fun (fieldName, fieldExpr') -> (fieldName, T.getType fieldExpr')) |>
                Map.ofList
            let tau = T.RecordTy (maybePacked', tauFields)
            adorn posE tau (T.RecordExp {packed=isPacked; initFields=fieldExprs'}) c''
        | Ast.RefExp ((pose, _) as expr) ->
            let (expr', c') = ty expr
            let tau = T.ConApp (T.RefTy, [Choice1Of2 (T.getType expr')])
            adorn posE tau (T.RefExp expr') c'
        | Ast.Smartpointer (ptr, destructor) ->
            let (ptr', c1) = ty ptr
            let (destructor', c2) = ty destructor
            let closureTy = ClosureTy Map.empty
            let destructorTy = T.ConApp (T.FunTy, [Choice1Of2 closureTy; Choice1Of2 T.unittype; Choice1Of2 T.rawpointertype])
            let c3 = T.getType ptr' =~= (T.rawpointertype, errStr [A.getPos ptr] "First argument to smartpointer keyword must be of type rawpointer")
            let c4 = T.getType destructor' =~= (destructorTy, errStr [A.getPos destructor] "Second argument to smartpointer keyword must be a destructor of type (||)(rawpointer) -> unit")
            let c' = c1 &&& c2 &&& c3 &&& c4
            adorn posE (T.TyPointer |> T.BaseTy |> T.TyCon) (T.Smartpointer (ptr', destructor')) c'
        | Ast.SequenceExp (poss, exps) ->
            let ((pose, _) as exp)::rest = exps
            let (exp', c1) = ty exp
            let (localVars', gamma', c2) =
                match exp with
                | (_, Ast.LetExp {left=left; right=right}) ->
                    // The constraints are already included in c1 above
                    let (_, c2, localVars', gamma') = checkPattern left (T.getType exp')
                    (Set.union localVars localVars', gamma', c2)
                | (_, Ast.DeclVarExp {varName=varName; typ=typ}) ->
                    let gamma' = Map.add (A.unwrap varName) (true, T.Forall (emptytemplate, [], T.getType exp')) gamma
                    (Set.add (A.unwrap varName) localVars, gamma', Trivial)
                | _ ->
                    (localVars, gamma, Trivial)

            let (tau, rest', c3)  =
                if List.isEmpty rest then
                    // Last thing in the sequence
                    // so the type of the sequence is the type
                    // of the expression
                    (T.getType exp', [], Trivial)
                else
                    // Not the last thing in the sequence
                    // so the type of the sequence is the type
                    // of the rest
                    let ((_, tau, T.SequenceExp rest'), c3) = typeof (poss, Ast.SequenceExp (poss, rest)) denv dtenv menv localVars' ienv tyVarMapping capVarMapping gamma'
                    (tau, rest', c3)
                    
            let c' = c1 &&& c2 &&& c3
            adorn posE tau (T.SequenceExp (exp'::rest')) c'
        | Ast.CharListLiteral (pos, str) ->
            let codePoints =
                (String.explode str |> List.map (fun c -> int64(c))) @ [0L] |>
                List.map (fun c -> (pos, (pos, c) |> A.UInt8Exp))
            let len = int64 (String.length str + 1)
            // Convert the string literal into a list of uint8s
            ty (pos, A.RecordExp {packed=None;
                                  initFields=(pos, [((pos, "data"), (pos, A.ArrayLitExp (pos, codePoints)));
                                                    ((pos, "length"), (pos, A.UInt32Exp (pos, len)))])})
        | A.StringLiteral (pos, str) ->
            adorn posE T.stringtype (T.StringExp str) Trivial
        | Ast.TupleExp exprs ->
            let (exprs', c') = typesof exprs dtenv menv localVars gamma
            let subTaus = List.map (T.getType >> Choice1Of2) exprs'
            let tau = T.ConApp (T.TupleTy, subTaus)
            adorn posE tau (T.TupleExp exprs') c'
        | Ast.TypeConstraint {exp=(pose, _) as exp; typ=(post, _) as typ} ->
            let (exp', c1) = ty exp
            let c' = c1 &&& (convertType' typ =~= (T.getType exp', errStr [pose; post] "Type constraint could not be satisfied"))
            adorn posE (T.getType exp') (T.unwrap exp') c'
        | Ast.UnaryOpExp {op=(poso, op); exp=(pose, _) as exp} ->
            let (exp', c1) = ty exp
            let (op', c2, tau) =
                match op with
                | Ast.LogicalNot ->
                    (T.LogicalNot, T.booltype =~= (T.getType exp', errStr [pose] "The type of an expression applied to a logical not operation must be a boolean"), T.booltype)
                | Ast.BitwiseNot ->
                    let c3 = InterfaceConstraint (T.getType exp', T.IsInt, errStr [pose] "Bitwise not operator argument must be a of integer type")
                    (T.BitwiseNot, c3, T.getType exp')
                | Ast.Negate ->
                    let c3 = InterfaceConstraint (T.getType exp', T.IsNum, errStr [pose] "Negation operator argument must be a number")
                    (T.Negate, c3, T.getType exp')
                | Ast.Deref ->
                    let retTau = freshtyvar ()
                    let c' = (T.ConApp (T.RefTy, [Choice1Of2 retTau]) =~= (T.getType exp', errStr [pose] "Attempting to dereference an expression with a non-ref type."))
                    (T.Deref, c', retTau)
            let c' = c1 &&& c2
            adorn posE tau (T.UnaryOpExp {op=op'; exp=exp'}) c'
        | Ast.NullExp (posN, ()) ->
            adorn posN T.rawpointertype T.NullExp Trivial
    ty (posE, e)

let checkUnderscores typ =
    match findUnderscoreTys typ with
    | [] -> ()
    | underscores ->
        raise <| SemanticError ((errStr underscores "Underscore type expressions are not allowed in type declarations. Note that function types without an explicit closure type are desugared into a type expression containing an underscore. For example, (a) -> b is syntax sugar for (_)(a) -> b.").Force())

// Check for unknown type variables on the right hand side
let checkUnknownVars menv denv (maybeTemplate : Ast.Template option) (kind : T.Kind) typ =
    let varsFun =
        match kind with
        | T.StarKind -> tyVars
        | T.IntKind -> capVars
    match varsFun menv denv T.StarKind (A.unwrap typ) with
    | [] -> ()
    | tyVarsRhs ->
        let tyVarsLhs =
            match maybeTemplate with
            | Some (_, templateVars) ->
                templateVars |> List.map (fst >> A.unwrap) |> Set.ofList
            | None ->
                Set.empty
        tyVarsRhs |>
        List.iter
            (fun (posr, rhsVarName) ->
                if Set.contains rhsVarName tyVarsLhs then
                    ()
                else
                    let errMsg =
                        match kind with
                        | T.StarKind -> sprintf "Unknown type variable '%s' on right hand side of the type declaration. Did you forget to add this variable to the template on the left hand side?" rhsVarName
                        | T.IntKind -> sprintf "Unknown capacity variable '%s' on right hand side of the type declaration. Did you forget to add this variable to the template on the left hand side?" rhsVarName
                    raise <| SemanticError ((errStr [posr] errMsg).Force()))

// This function may seem insanely complicated, but really what it's doing
// is quite simple. To understand this function, I suggest understanding
// how constraint based type solving works, as well as understanding some basic
// graph theory concepts such as strongly connected components, the condensation graph
// and topological ordering. The first part of this function consists of analyzing
// the modules to build up environments used in type checking. The second part
// involves a graph theoretical/topological ordering analysis.
let typecheckProgram (program : Ast.Module list) (fnames : string list) (keepUnreachable : bool) =
    // modNamesToMods maps module names to module contents
    let modNamesToMods =
        let names =
            List.zip program fnames |>
            List.map (fun (module_, fname) ->
                match nameInModule module_ with
                | Some name -> Ast.unwrap name
                | None -> raise <| SemanticError [Error.ErrMsg (sprintf "Semantic error in %s: The module does not contain exactly one module declaration." fname)])
        Map.ofList (List.zip names program)
    
    // valueDecsSet is a set of all fully qualified value declarations in all modules
    let valueDecsSet =
        program |> List.map (fun decs ->
            let modName = nameInModule decs |> Option.get |> Ast.unwrap
            let valNames = valueDecsInModule decs
            List.zip
                (List.map (fun _ -> modName) valNames)
                valNames) |> List.concat |> Set.ofList

    // A menv maps names in a module to their full module qualifier
    // modNamesToMenvs stores these maps for every module
    let modNamesToMenvs =
        // maps names to module qualifiers
        let menvs0 = (List.map (fun (Ast.Module decs) ->
            let modName = nameInModule (Ast.Module decs) |> Option.get |> Ast.unwrap
            let typeNames = typesInModule (Ast.Module decs)
            let valNames = valueDecsInModule (Ast.Module decs)
            // Find the names of all of the value constructors as well
            let valConNames =
                decs |> List.map Ast.unwrap |> List.filter isUnionDec |>
                List.map
                    (fun (Ast.UnionDec {valCons=(_, valCons)}) -> valCons |> List.map (fun ((_, name), _) -> name)) |>
                List.concat
            let names = typeNames @ valNames @ valConNames
            match Seq.duplicates names with
            | dups when Seq.length dups = 0 ->
                List.fold (fun map2 name ->
                    Map.add name (modName, name) map2
                ) Map.empty names
            | dups ->
                let dupsStr = String.concat ", " dups
                raise <| SemanticError [Error.ErrMsg (sprintf "Semantic error in module %s: The following declarations have duplicate definitions: %s" modName dupsStr)]
        ) program)

        let modNamesToMenvs0 = Map.ofList (List.zip (List.map (nameInModule >> Option.get >> Ast.unwrap) program) menvs0)

        // Merge the menvs together based on the open declarations
        (Map.map (fun modName menv0 ->
            let allOpens = List.map Ast.unwrap (opensInModule (Map.find modName modNamesToMods))
            List.fold (fun menv1 nameToMerge ->
                match Map.tryFind nameToMerge modNamesToMenvs0 with
                | Some menv' -> Map.merge menv' menv1 
                | None -> raise <| SemanticError [Error.ErrMsg (sprintf "Semantic error: Module %s opens %s, which does not exist." modName nameToMerge)]
            ) menv0 allOpens
        ) modNamesToMenvs0)
    
    // Maps module qualifiers to their actual declarations
    let denv = (List.fold (fun map (Ast.Module decs) ->
        let modName = nameInModule (Ast.Module decs) |> Option.get
        let namedDecs = List.filter (Ast.unwrap >> isNamedDec) decs
        List.fold (fun map2 dec0 ->
            let decName = nameOfDec (Ast.unwrap dec0)
            let qual = (Ast.unwrap modName, Ast.unwrap decName)
            Map.add qual dec0 map2) map namedDecs
    ) Map.empty program)

    // ienv maps value constructor's module qualifiers to their index
    // the index is based on the order in which the constructor appears
    // in the algebraic datatype declaration.
    let ienv = (Map.fold (fun accumIenv ((module_, name) as modQual) d ->
        match Ast.unwrap d with
        | Ast.UnionDec {valCons=(_, valCons)} ->
            (List.mapi (fun i ((_, valConName), _) ->
                (valConName, i)
            ) valCons) |>
            (List.fold (fun accumIenv' (valConName, i) ->
                Map.add (module_, valConName) i accumIenv')
            accumIenv)
        | _ ->
            accumIenv
    ) Map.empty denv)

    // Populate the declaration type environment with all aliases, value constructors
    // and type declarations
    let dtenv0 = (Map.fold (fun accumDtenv0 ((module_, name) as modQual) d ->
        let menv = Map.find module_ modNamesToMenvs

        match Ast.unwrap d with
        | Ast.AliasDec {template=maybeTemplate; typ=typ} ->
            checkUnderscores typ
            checkUnknownVars menv denv maybeTemplate T.StarKind typ
            checkUnknownVars menv denv maybeTemplate T.IntKind typ
            match tyVars menv denv T.StarKind (A.unwrap typ) with
            | [] -> ()
            | tyVarsRhs ->
                let tyVarsLhs =
                    match maybeTemplate with
                    | Some (_, templateVars) ->
                        templateVars |> List.map (fst >> A.unwrap) |> Set.ofList
                    | None ->
                        Set.empty
                tyVarsRhs |>
                List.iter
                    (fun (posr, rhsVarName) ->
                        if Set.contains rhsVarName tyVarsLhs then
                            ()
                        else
                            raise <| SemanticError ((errStr [posr] (sprintf "Unknown type variable %s on right hand side of the type alias. Did you forget to add this variable to the template on the left hand side?" rhsVarName)).Force()))
            let (templateVars', (tyVarMapping, capVarMapping)) =
                match maybeTemplate with
                | Some (_, templateVars) ->
                    List.mapFold
                        (fun (accumTyVarMapping, accumCapVarMapping) ((_, templateVarName), kind) ->
                            match kind with
                            | A.StarKind _ ->
                                let (T.TyVar freshName) as t' = freshtyvar ()
                                let accumTyVarMapping' = Map.add templateVarName t' accumTyVarMapping
                                ((freshName, T.StarKind), (accumTyVarMapping', accumCapVarMapping))
                            | A.IntKind _ ->
                                let (T.CapacityVar freshName) as c' = freshcapvar ()
                                let accumCapVarMapping' = Map.add templateVarName c' accumCapVarMapping
                                ((freshName, T.IntKind), (accumTyVarMapping, accumCapVarMapping')))
                        (Map.empty, Map.empty)
                        templateVars
                | None ->
                    ([], (Map.empty, Map.empty))
            let typ' = convertType menv denv Map.empty tyVarMapping capVarMapping typ
            let aliasDecTy = T.AliasDecTy (templateVars', typ')
            Map.add modQual aliasDecTy accumDtenv0
        | Ast.UnionDec {valCons=(_, valCons); template=maybeTemplate} ->
            let template' =
                match maybeTemplate with
                | None ->
                    []
                | Some (_, templateVars) ->
                    templateVars |>
                    List.map
                        (function
                        | ((_, varName), A.StarKind _) -> (varName, T.StarKind)
                        | ((_, varName), A.IntKind _) -> (varName, T.IntKind))
            let udecty = T.UnionDecTy (template', {module_=module_; name=name})
            // Generate the type of the algebraic datatype
            let retTyBase = T.ModuleQualifierTy {module_=module_; name=name}
            let retTy =
                match maybeTemplate with
                | None -> T.TyCon retTyBase
                | Some (_, templateVars) ->
                    let templateVars' =
                        templateVars |>
                        List.map
                            (function
                            | ((_, varName), A.StarKind _) -> Choice1Of2 (T.TyVar varName)
                            | ((_, varName), A.IntKind _) -> Choice2Of2 (T.CapacityVar varName))
                    T.ConApp (retTyBase, templateVars')
            // Convert all value constructors into function declarations
            // All value constructors have empty closures
            let closureTy = T.ClosureTy Map.empty
            let accumDtenv2 = valCons |> (List.fold (fun accumDtenv1 ((_, valConName), innerTys) ->
                innerTys |> List.iter checkUnderscores
                innerTys |> List.iter (checkUnknownVars menv denv maybeTemplate T.StarKind)
                innerTys |> List.iter (checkUnknownVars menv denv maybeTemplate T.IntKind)
                // Convert the types given in each value constructor to a T.TyExpr
                let paramTy = List.map (convertType menv denv Map.empty Map.empty Map.empty) innerTys
                // Create the FunDecTy for this specific value constructor
                let ts = T.FunDecTy <| T.Forall (template', [], funty closureTy retTy paramTy)
                Map.add (module_, valConName) ts accumDtenv1
            ) accumDtenv0)
            Map.add modQual udecty accumDtenv2
        | _ ->
            accumDtenv0
    ) Map.empty denv)

    // Check the dependency graph first to determine what order we need to typecheck in (topological sort)
    let valueGraph = new QuikGraph.AdjacencyGraph<string*string, QuikGraph.Edge<string*string>>()

    // Add vertices to the graph
    program |> List.iter (fun moduledef ->
        let module_ = nameInModule moduledef |> Option.get |> Ast.unwrap
        // List of all let and function declarations in
        // the module currently being considered
        let valueDecs = valueDecsInModule moduledef
        // Add all the declarations as vertices to the graph
        valueDecs |> List.iter (fun name ->
            valueGraph.AddVertex((module_, name)) |> ignore
        ))

    let mutable maybeSetupModule = None
    let mutable maybeLoopModule = None

    // Add edges to the graph
    program |> List.iter (fun moduledef ->
        let module_ = nameInModule moduledef |> Option.get |> Ast.unwrap
        // List of all let and function declarations in
        // the module currently being considered
        let valueDecs = valueDecsInModule moduledef
        let menv = Map.find module_ modNamesToMenvs
        // Find out what declarations this declaration refers to
        valueDecs |> List.iter (fun name ->
            let (pos, dec) = Map.find (module_, name) denv
            let references =
                match dec with
                | (Ast.FunctionDec {clause=(_, {body=(_, expr); arguments=(_, arguments)})}) ->
                    if name = "setup" then
                        maybeSetupModule <- Some module_
                    elif name = "loop" then
                        maybeLoopModule <- Some module_
                    else
                        ()
                    // We need to determine what local variables this function declares so that we know what variables
                    // to ignore if we find a reference to that name
                    // Get the function's argument names
                    let a1 = arguments |> List.map (fst >> Ast.unwrap) |> Set.ofList
                    // Capacities are local variables as well!
                    let convertType' = convertType menv denv dtenv0 Map.empty Map.empty
                    let argumentsTypes = arguments |> List.map snd |> List.filter Option.isSome |> List.map (Option.get >> convertType')
                    let a2 = argumentsTypes |> List.map (Constraint.freeVars >> snd) |> Set.unionMany
                    let localVars = Set.union a1 a2
                    decRefs valueDecsSet menv localVars expr
                | Ast.LetDec {right=(_, expr)} ->
                    decRefs valueDecsSet menv Set.empty expr
            // Add all the edges to the graph
            references |> Set.iter (fun reference ->
                if Map.containsKey reference denv then
                    valueGraph.AddEdge(new QuikGraph.Edge<string*string>((module_, name), reference)) |> ignore
                else
                    raise <| TypeError ((errStr [pos] (sprintf "Reference made to %s:%s which could not be found" (fst reference) (snd reference))).Force())
            )
        )
    )

    let reachable startNode =
        let rec reachableRec visitedAlready startNode =
            if Set.contains startNode visitedAlready then
                visitedAlready
            else
                let mutable visitedAlready' = Set.add startNode visitedAlready
                valueGraph.OutEdges(startNode) |>
                Seq.fold (fun accumVisitedAlready outEdge -> reachableRec accumVisitedAlready outEdge.Target) visitedAlready'
        reachableRec Set.empty startNode

    if not keepUnreachable then
        match (maybeSetupModule, maybeLoopModule) with
        | (Some setupModule, Some loopModule) ->
            let reachable = Set.union (reachable (setupModule, "setup")) (reachable (loopModule, "loop"))
            for modQual in valueGraph.Vertices do
                if not (Set.contains modQual reachable) then
                    valueGraph.RemoveVertex(modQual) |> ignore
        | (None, _) ->
            raise <| SemanticError [Error.ErrMsg "Unable to find program entry point. Please create a function called setup.\n fun setup() = ()"]
        | (_, None) ->
            raise <| SemanticError [Error.ErrMsg "Unable to find program entry point. Please create a function called loop.\n fun loop() = ()."]

    // Also build a dependency graph for the types
    let typeGraph = new QuikGraph.AdjacencyGraph<string*string, QuikGraph.Edge<string*string>>()

    program |> List.iter (fun moduledef ->
        let (Ast.Module decs) = moduledef
        let module_ = nameInModule moduledef |> Option.get |> Ast.unwrap
        // List of all algebraic and alias datatypes in
        // the module currently being considered
        let typeDecs = typesInModule moduledef
        let menv = Map.find module_ modNamesToMenvs
        // Add all the declarations as vertices to the graph
        typeDecs |> List.iter (fun name ->
            typeGraph.AddVertex((module_, name)) |> ignore
            let (pos, dec) = Map.find (module_, name) denv
            let references = tyRefs menv dec
            references |> Set.iter (fun reference ->
                match Map.tryFind reference dtenv0 with
                | (Some (T.UnionDecTy _) | Some (T.AliasDecTy _)) ->
                    typeGraph.AddEdge(new QuikGraph.Edge<string*string>((module_, name), reference)) |> ignore
                | _ ->
                    raise <| TypeError ((errStr [pos] (sprintf "Reference made to %s:%s which could not be found" (fst reference) (snd reference))).Force()))))                    
    
    // Determine what order the types should appear in (reverse topological order)
    let typeDependencyOrder =
        // Ensure that there are no circular type dependencies
        // The type graph should be a DAG
        let typeCondensation = typeGraph.CondensateStronglyConnected<_, _, QuikGraph.AdjacencyGraph<_, _>>()
        typeCondensation.Vertices |>
        Seq.iter
            (fun scc ->
                let sccStr = lazy (scc.Vertices |> Seq.map (fun (m, n) -> sprintf "%s:%s" m n) |> String.concat ", ")
                // Check for mutually recursive types
                if Seq.length scc.Vertices > 1 then
                    raise <| TypeError [Error.ErrMsg (sprintf "Semantic error: The following type declarations form an unresolvable dependency cycle: %s" (sccStr.Force()))]
                // Check for self-referential types
                elif Seq.length scc.Edges > 0 then
                    raise <| TypeError [Error.ErrMsg (sprintf "Semantic error: The following type refers to itself: %s" (sccStr.Force()))])
        typeGraph.TopologicalSort() |> Seq.rev |> List.ofSeq

    let includeDecs = 
        program |>
        List.map (fun (Ast.Module decs) -> List.filter (Ast.unwrap >> isInclude) decs) |>
        List.concat |>
        List.map (fun (_, Ast.IncludeDec (_, includes)) ->
            T.IncludeDec (List.map Ast.unwrap includes))

    let openDecs = 
        program |>
        List.map (fun (Ast.Module decs) ->
            let module_ = nameInModule (Ast.Module decs) |> Option.get |> Ast.unwrap
            let opens = List.filter (Ast.unwrap >> isOpen) decs
            let moduleNames = List.map (fun _ -> module_) opens
            List.zip moduleNames opens) |>
        List.concat |>
        List.map (fun (module_, (_, Ast.OpenDec (_, openModules))) ->
            (module_, T.OpenDec (List.map Ast.unwrap openModules)))
    
    let moduleNames = program |> List.map (fun decs -> nameInModule decs |> Option.get |> Ast.unwrap)

    let typeDecs =
        let unorderedDecs =
            program |>
            List.map (fun (Ast.Module decs) ->
                let module_ = nameInModule (Ast.Module decs) |> Option.get |> Ast.unwrap
                let types = List.filter (Ast.unwrap >> isTypeDec) decs
                types |> List.map (fun typ -> (module_, typ))) |>
            List.concat |>
            List.map (fun (module_, (_, dec)) ->
                let menv = Map.find module_ modNamesToMenvs
                match dec with
                | Ast.UnionDec {name=(_, name); valCons=(_, valCons); template=template} ->
                    let valCons' =
                        valCons |> List.map (fun ((_, valConName), argTypes) ->
                            let argTypes' = List.map (convertType menv denv dtenv0 Map.empty Map.empty) argTypes
                            (valConName, argTypes'))
                    let ret = (module_, T.UnionDec {name=name; template=Option.map convertTemplate template; valCons=valCons'})
                    ((module_, name), ret)
                | Ast.AliasDec {name=(_, name); template=template; typ=typ} ->
                    let typ' = convertType menv denv dtenv0 Map.empty Map.empty typ
                    let ret = (module_, T.AliasDec {name=name; template=Option.map convertTemplate template; typ=typ'})
                    ((module_, name), ret))|>
            Map.ofList
        // Put the declarations into dependency order (reverse topological order)
        List.map (fun modQual -> Map.find modQual unorderedDecs) typeDependencyOrder
    
    // A list of all top level inline code uses, given in a list of (moduleName, T.InlineCodeDec code)
    let inlineCodeDecs = 
        program |>
        List.map (fun (Ast.Module decs) ->
            let module_ = nameInModule (Ast.Module decs) |> Option.get |> Ast.unwrap
            let inlineCode = List.filter (Ast.unwrap >> isInlineCodeDec) decs
            let moduleNames = List.map (fun _ -> module_) inlineCode
            List.zip moduleNames inlineCode) |>
        List.concat |>
        List.map (fun (module_, (_, Ast.InlineCodeDec (_, code))) ->
            (module_, T.InlineCodeDec code))
    
    let connectedComponents = new System.Collections.Generic.Dictionary<string * string, int>()
    valueGraph.StronglyConnectedComponents(connectedComponents) |> ignore

    let sccs = connectedComponents |> Map.ofDict |> Map.invertNonInjective |> Map.toList |> List.map snd

    // Now verify that each SCC either contains all functions or just a single let
    sccs |>
    List.iter
        (fun scc ->
            let sccStr = scc |> List.map (fun (m, n) -> sprintf "%s:%s" m n) |> String.concat ", "
            match scc with
            | [x] when isLet (Ast.unwrap (Map.find x denv)) ->
                ()
            | _ ->
                scc |> List.iter
                    (fun decref ->
                        if isLet (Ast.unwrap (Map.find decref denv)) then
                            let (module_, name) = decref
                            raise <| TypeError [Error.ErrMsg (sprintf "Semantic error: The let named '%s' in module '%s' has a self reference. The following declarations form an unresolvable dependency cycle: %s" name module_ sccStr)]
                        else
                            ()))
    
    let condensation = valueGraph.CondensateStronglyConnected<_, _, QuikGraph.AdjacencyGraph<_, _>>()
    let dependencyOrder = condensation.TopologicalSort() |> Seq.map (fun scc -> scc.Vertices |> List.ofSeq) |> Seq.rev |> List.ofSeq

    // Given an accumulated global type environment (ie, one that maps module qualifiers
    // to type schemes), constructs a local type environment based on what that module
    // opens from other modules. The local environment maps names to type schemes
    let localGamma (globalGamma : Map<(string * string), TyScheme>) (module_ : string) : Map<string, (bool * TyScheme)> =
        let menv = Map.find module_ modNamesToMenvs
        (Map.fold (fun gammaAccum localName moduleQual ->
            match Map.tryFind moduleQual globalGamma with
            | Some ty ->
                Map.add localName (false, ty) gammaAccum
            | None ->
                gammaAccum
        ) Map.empty menv)

    // Initialize the global type environment (gamma) with the value constructor's type schemes
    let globalGammaInit =
        program |> List.map (fun (Ast.Module decs) ->
            let module_ = nameInModule (Ast.Module decs) |> Option.get |> Ast.unwrap
            decs |> List.map Ast.unwrap |> List.filter isUnionDec |>
            List.map
                (fun (Ast.UnionDec {valCons=(_, valCons)}) ->
                    valCons |> List.map (fun ((_, name), _) ->
                        let modqual = (module_, name)
                        let (T.FunDecTy scheme) = Map.find modqual dtenv0
                        (modqual, scheme))) |>
            List.concat) |> List.concat |> Map.ofList
    
    // We are now ready to do the type checking
    // We will do each SCC one at a time and accumulate the inferred types via a global
    // type environment called globalGamma
    let (checkedDecs, _) =
        dependencyOrder |> List.mapFold
            (fun (dtenv, globalGamma) scc ->
                match scc with
                // Found a SCC containing a single let statement
                | [(module_, name) as modqual] when isLet (Ast.unwrap (Map.find modqual denv)) ->
                    // Look up the actual declaration of the let statement we are currently type checking
                    let (posl, Ast.LetDec {varName=varName; typ=typ; right=right}) = Map.find modqual denv
                    // Get the menv of the module containing the let statement
                    let menv = Map.find module_ modNamesToMenvs
                    let localVars = Set.empty
                    let gamma = localGamma globalGamma module_
                    // Generate the constraints for the right hand side of the let statement
                    let (right', c1) = typeof right denv dtenv menv localVars ienv Map.empty Map.empty gamma
                    // If the let statement has a type constraint in its definition, we need to ensure
                    // that the type of right' equals the constraint
                    let c2 =
                        match typ with
                        | Some ((post, _) as ty) ->
                            // There was a type constraint given by the user on the let statement
                            // Generate a fresh constraint for this restriction
                            T.getType right' =~= (convertType menv denv dtenv Map.empty Map.empty ty, errStr [post; Ast.getPos right] "The type of the right hand side of the let expression violates the given type constraint.")
                        | None ->
                            // No constraint was given by the user
                            Trivial
                    let c = c1 &&& c2
                    // Solve for the system of constraints
                    let (theta, kappa, interfaceConstraintMap) = solve c []
                    let tau = tycapsubst theta kappa (T.getType right')
                    // Generalize (universally quantify) all free types for this let statement
                    let elabtau = generalize interfaceConstraintMap tau
                    // Top level let statements are currently not allowed to be polymorphic
                    // TODO: Remove this restriction once Arduino IDE turns on C++14
                    match elabtau with
                    | T.Forall ([], _, _) ->
                        ()
                    | _ ->
                        raise <| TypeError ((errStr [posl] (sprintf "Let declaration was inferred to have the following type scheme:\n\n%s\n\nTop level let declarations do not support values of polymorphic type. Once the Arduino IDE turns on C++14 by default this may change (variable templates). In the meantime, consider either removing the polymorphism, add a type annotation, or wrap your variable in a function." (schemeString elabtau))).Force())
                    // Check if there is any polymorphic variables within the let statement's right
                    // hand side. This type of free polymorphism is not allowed
                    match AstAnalysis.findFreeVars theta kappa right' with
                    | ([], []) ->
                        ()
                    | ((badPos, _)::_, _) ->
                        raise <| TypeError ((errStr [badPos] "Too much polymorphism! The following expression has a type that was detected to contain a type variable. Consider adding a type constraint to fix the source of this problem").Force())
                    | (_, (badPos, _)::_) ->
                        raise <| TypeError ((errStr [badPos] "Too much polymorphism! The following expression has a capacity that was detected to contain a capacity variable. Consider adding a type constraint to fix the source of this problem").Force())
                    let globalGamma' = Map.add modqual elabtau globalGamma
                    let dtenv' = Map.add modqual (T.LetDecTy tau) dtenv
                    let let' = T.LetDec {varName=name; typ=tau; right=right'}
                    (([(module_, let')], theta, kappa), (dtenv', globalGamma'))
                // Found a SCC containing mutually recursive function(s)
                | _ ->
                    // Create a fresh type variable for every function in the SCC. This will
                    // represent the type of each function. Note that this also means that
                    // polymorphic recursion is not supported
                    let alphas = List.map freshtyvar scc
                    // Create a scheme for each fresh type variable
                    let alphaSchemes = List.map (fun a -> T.Forall (emptytemplate, [], a)) alphas
                    // Add all of these type schemes to the global gamma
                    let tempGlobalGamma =
                        List.fold (fun globalGammaAccum (modqual, alphaScheme) ->
                            Map.add modqual alphaScheme globalGammaAccum
                        ) globalGamma (List.zip scc alphaSchemes)
                    // Create local gammas for every entry in the SCC
                    let tempGammas = List.map (fst >> localGamma tempGlobalGamma) scc
                    // Create a dtenv containing all of our temporary type schemes
                    let tempdtenv =
                        List.fold (fun accumdtenv (modqual, alphaScheme) ->
                            Map.add modqual (T.FunDecTy alphaScheme) accumdtenv
                        ) dtenv (List.zip scc alphaSchemes)
                    let (funDecsInfo, terminalCaps, cs) =
                        List.zip3 scc tempGammas alphas |>
                        // Generate constraints for each function in the SCC
                        List.map
                            (fun ((module_, name) as modqual, tempGamma, alpha) ->
                                // Look up the actual function definition based on the module qualifier
                                let (posf, Ast.FunctionDec {clause=(posc, {arguments=(posa, arguments); body=body; returnTy=maybeReturnTy; interfaceConstraints=(posi, interfaceConstraints) })}) = Map.find modqual denv
                                // Lookup the menv (which maps local names to full module qualifiers)
                                let menv = Map.find module_ modNamesToMenvs
                                // Extract the function parameter names and save it in a set
                                let localArguments = List.map (fst >> Ast.unwrap) arguments |> Set.ofList
                                // Check if all the argument names are unique
                                if Set.count localArguments = List.length arguments then
                                    ()
                                else
                                    raise <| TypeError ((errStr [posa] "There are duplicate argument names").Force())

                                // Determine what the user defined free type variables and free capacities are
                                let convertType' = convertType menv denv tempdtenv Map.empty Map.empty

                                // Generate types for all arguments. If the user gave an explicit type annotation, use
                                // that, otherwise generate a fresh type variable for that argument.
                                let argTys =
                                    arguments |>
                                    List.map
                                        (fun (_, maybeTy) ->
                                            match maybeTy with
                                            | Some ((post, _) as ty) -> convertType' ty
                                            | None -> freshtyvar ())
                                
                                let retTy =
                                    match maybeReturnTy with
                                    | Some ty -> convertType' ty
                                    | None -> freshtyvar ()

                                let (manyFreeTyVars, manyFreeCapVars) = (retTy::argTys) |> List.map Constraint.freeVars |> List.unzip
                                let freeTyVars = Set.unionMany manyFreeTyVars |> List.ofSeq
                                let freeCapVars = Set.unionMany manyFreeCapVars |> List.ofSeq

                                // Give fresh names to all type variables and capacity variables used in the arguments
                                // this will remove any user defined names, which could collide if the same names are used
                                // across multiple functions
                                let freshTyVars = freeTyVars |> List.map freshtyvar
                                let freshCapVars = freeCapVars |> List.map freshcapvar

                                let tyVarMapping = List.zip freeTyVars freshTyVars |> Map.ofList
                                let capVarMapping = List.zip freeCapVars freshCapVars |> Map.ofList

                                // Determine what the user defined type and capacity variables are. Note that this isn't the same as
                                // freeTyVars, because Constraint.freeVars will create fresh type variables for type expressions with underscores
                                let userTyVarsArgs =
                                    arguments |>
                                    List.map
                                        (fun (_, maybeTy) ->
                                            match maybeTy with
                                            | Some ty -> AstAnalysis.tyVars menv denv T.StarKind (A.unwrap ty)
                                            | None -> []) |>
                                    List.concat

                                let userTyVarsRet =
                                    match maybeReturnTy with
                                    | Some ty -> AstAnalysis.tyVars menv denv T.StarKind (A.unwrap ty)
                                    | None -> []

                                let userCapVarsArgs =
                                    arguments |>
                                    List.map
                                        (fun (_, maybeTy) ->
                                            match maybeTy with
                                            | Some ty -> AstAnalysis.capVars menv denv T.StarKind (A.unwrap ty)
                                            | None -> []) |>
                                    List.concat

                                let userCapVarsRet =
                                    match maybeReturnTy with
                                    | Some ty -> AstAnalysis.capVars menv denv T.StarKind (A.unwrap ty)
                                    | None -> []

                                let userTyVars = userTyVarsArgs @ userTyVarsRet
                                let userCapVars = userCapVarsArgs @ userCapVarsRet

                                let userTyVarsNames = userTyVars |> List.map A.unwrap |> Set.ofList
                                let userCapVarsNames = userCapVars |> List.map A.unwrap |> Set.ofList

                                // userTyVarMapping maps user defined type variables to the fresh variable
                                let userTyVarMapping =
                                    userTyVars |>
                                    List.map
                                        (fun (posn, name) ->
                                            (name, (posn, Map.find name tyVarMapping))) |>
                                    Map.ofList

                                // userCapVarMapping maps user defined capacity variables to the fresh variable
                                let userCapVarMapping =
                                    userCapVars |>
                                    List.map
                                        (fun (posn, name) ->
                                            (name, (posn, Map.find name capVarMapping))) |>
                                    Map.ofList

                                let terminalCaps =
                                    userCapVarMapping |>
                                    Map.values |>
                                    Seq.map (A.unwrap >> (fun (T.CapacityVar name) -> name)) |>
                                    List.ofSeq

                                // Replace all user defined names in the argument types with fresh variables
                                let argTys' = argTys |> List.map (Constraint.tycapsubst tyVarMapping capVarMapping)
                                let retTy' = Constraint.tycapsubst tyVarMapping capVarMapping retTy

                                // Add any capacity variables as local variables
                                let localVars = Set.union localArguments userCapVarsNames
                                // Add the arguments to the type environment (gamma)
                                let tempGamma' =
                                    List.zip arguments argTys' |>
                                    List.fold
                                        (fun accumTempGamma' (((_, name), _), argTy) ->
                                            let argTyScheme = T.Forall (emptytemplate, [], argTy)
                                            Map.add name (false, argTyScheme) accumTempGamma')
                                        tempGamma
                                // Add the capacities to the type environment
                                let tempGamma'' =
                                    userCapVarsNames |>
                                    Set.fold
                                        (fun accum capVarName ->
                                            Map.add capVarName (false, T.Forall (emptytemplate, [], T.int32type)) accum)
                                        tempGamma'
                                // Finally typecheck the body
                                let (body', c1) = typeof body denv tempdtenv menv localVars ienv tyVarMapping capVarMapping tempGamma''
                                let closureTy = T.ClosureTy Map.empty
                                // Constrain alpha to be equal to the type of the body
                                let c2 = alpha =~= (funty closureTy (T.getType body') argTys', errStr [posf] "The inferred type of the function violated a constraint based on the function declaration")
                                // If the user gave an explicit return type, we need to generate a constraint for that
                                let c3Pos =
                                    match maybeReturnTy with
                                    | Some (post, _) -> [posf; post]
                                    | None -> [posf]
                                let c3 = retTy' =~= ((T.getType body'), errStr c3Pos "The type of the body did not match the type of the return constraint")
                                // If the user gave explicit interface constraints, we need to generate constraints for those
                                let c4s =
                                    interfaceConstraints |>
                                    List.map (fun (posCon, (tau, (_, con))) ->
                                        let tau' = convertType menv denv tempdtenv tyVarMapping capVarMapping tau
                                        convertInterfaceConstraint menv denv tempdtenv con |>
                                        List.map (fun con' -> InterfaceConstraint (tau', con', errStr [posCon] "The specified type did not meet the interface constraint")) |>
                                        conjoinConstraints)
                                let c4 = conjoinConstraints c4s
                                let c = c1 &&& c2 &&& c3 &&& c4
                                let argNames = arguments |> List.map (fst >> Ast.unwrap)
                                ((modqual, userTyVarMapping, userCapVarMapping, argNames, argTys', T.getType body', body'), terminalCaps, c))
                            |> List.unzip3
                    let c = conjoinConstraints cs
                    let terminalCaps' = List.concat terminalCaps
                    // Solve the entire SCC at once
                    let (theta, kappa, interfaceConstraints) = solve c terminalCaps'
                    let (funDecs', (dtenv', globalGamma')) =
                        funDecsInfo |>
                        List.mapFold
                            (fun (accumDtenv', accumGlobalGamma') ((module_, name) as modqual, userTyVarMapping, userCapVarMapping, argNames, argTys, retTy, body') ->
                                userTyVarMapping |>
                                Map.iter
                                    (fun userGivenName (post, freshVar) ->
                                        match tycapsubst theta kappa freshVar with
                                        | T.TyVar _ ->
                                            ()
                                        | x ->
                                            raise <| TypeError ((errStr [post] (sprintf "The type parameter '%s' was inferred to be equivalent to the non-type variable '%s'" userGivenName (T.typeString x))).Force()))

                                userCapVarMapping |>
                                Map.iter
                                    (fun userGivenName (posc, freshCapVar) ->
                                        match simplifyCap (capsubst kappa freshCapVar) with
                                        | T.CapacityVar _ ->
                                            ()
                                        | x ->
                                            raise <| TypeError ((errStr [posc] (sprintf "The capacity parameter '%s' was inferred to be equivalent to the non-capacity variable '%s'" userGivenName (T.capacityString x))).Force()))
                                
                                let retTy' = tycapsubst theta kappa retTy
                                let argTys' = argTys |> List.map (tycapsubst theta kappa)
                                let arguments' = List.zip argNames argTys'

                                let funTy = funty emptyclosure retTy' argTys'
                                let (freets, freecs) = freeVars funTy
                                let t = List.ofSeq freets
                                let c = List.ofSeq freecs

                                // Now expand the set of type variables to account for interface field constraints
                                // this process is roughly equivalent to deriving functional dependency rules for record
                                // types. The type variables discovered during this process will be used in the next
                                // step only where we check for too much polymorphism. Example of the logic used here:
                                // Suppose we have an interface constraint 'a : { myField : 'b }, that is 'a is a type
                                // variable that is a record with a field named myField of type 'b. When detecting excess
                                // polymorphism, we would like to take into account that fixing a type for 'a also fixes
                                // its field type. In functional dependency terms, 'a -> 'b

                                // The return type of expandFunctionalDependency is (Set<string>*Set<string>), where the first
                                // set is the expanded type variables and the second is capacity variables
                                let rec expandFunctionalDependency (tyVar: string) : Set<string>*Set<string> =
                                    match Map.tryFind tyVar interfaceConstraints with
                                    | Some constraints ->
                                        let (extraTyVars, extraCapVars) =
                                            constraints |>
                                            List.map
                                                (fun (constraintType, _) ->
                                                    match constraintType with
                                                    | HasField (_, tau) ->
                                                        freeVars tau
                                                    | _ ->
                                                        (Set.empty, Set.empty)) |>
                                            List.unzip
                                        let (extraTyVars', extraCapVars') =
                                            extraTyVars |>
                                            Set.unionMany |>
                                            List.ofSeq |>
                                            List.map (expandFunctionalDependency) |>
                                            List.unzip
                                        let extraTyVars'' = Set.union (Set.unionMany extraTyVars') (Set.unionMany extraTyVars)
                                        let extraCapVars'' = Set.union (Set.unionMany extraCapVars') (Set.unionMany extraCapVars)
                                        (Set.add tyVar extraTyVars'', extraCapVars'')
                                    | None ->
                                        (Set.singleton tyVar, Set.empty)
                                let (funDepsTs, funDepsCs) = t |> List.map expandFunctionalDependency |> List.unzip
                                let funDepsTs' = Set.unionMany funDepsTs
                                let funDepsCs' = Set.union (Set.ofList c) (Set.unionMany funDepsCs)
                                // Now check to see if any of the interface constraints contain free variables
                                // that are not also members of the template. If this is the case, there is
                                // polymorphism within the function that cannot be reified by inferring either the
                                // arguments or return types. This is an error
                                match Set.difference (Map.keys interfaceConstraints) funDepsTs' |> List.ofSeq with
                                | [] -> ()
                                | badFreeVar::_ ->
                                    let (_, errMsg)::_ = Map.find badFreeVar interfaceConstraints
                                    raise <| TypeError ([Error.ErrMsg (sprintf "Too much polymorphism! A polymorphic interface constraint was detected containing a type variable that would not be reified by fixing either the argument types or return types. Consider adding a type constraint to fix the source of this problem.")] @ errMsg.Force())
                                let (freeTyVarsInBody, freeCapVarsInBody) = AstAnalysis.findFreeVars theta kappa body'
                                match Set.difference (List.map A.unwrap freeTyVarsInBody |> Set.ofList) funDepsTs' |> List.ofSeq with
                                | [] -> ()
                                | badFreeVar::_ ->
                                    let (pos, _) = List.find (fun freeVar -> (A.unwrap freeVar) = badFreeVar) freeTyVarsInBody
                                    raise <| TypeError ((errStr [pos] "Too much polymorphism! The following expression has a type that was detected to contain a type variable that would not be reified by fixing either the argument types or return types. Consider adding a type constraint to fix the source of this problem").Force())
                                match Set.difference (List.map A.unwrap freeCapVarsInBody |> Set.ofList) funDepsCs' |> List.ofSeq with
                                | [] -> ()
                                | badFreeVar::_ ->
                                    let (pos, _) = List.find (fun freeVar -> (A.unwrap freeVar) = badFreeVar) freeCapVarsInBody
                                    raise <| TypeError ((errStr [pos] "Too much polymorphism! The following expression has a capacity that was detected to contain a capacity variable that would not be reified by fixing either the argument types or return types. Consider adding a type constraint to fix the source of this problem").Force())
                                
                                let (Forall (template, _, _)) as funScheme = generalize interfaceConstraints funTy

                                // The transformed body does not have user defined type variables anymore since
                                // everything was done with respect to fresh variables. Add these references back
                                // via a using statement
                                let tyUsings =
                                    Map.toList userTyVarMapping |>
                                    List.map
                                        (fun (originalTyVar, (post, newTyVar)) ->
                                            let resolvedTy = tycapsubst theta kappa newTyVar
                                            (post, T.unittype, T.InternalUsing {varName = originalTyVar; typ=resolvedTy}))
                                let capUsings =
                                    Map.toList userCapVarMapping |>
                                    List.map
                                        (fun (originalCapVar, (posc, newCapVar)) ->
                                            let resolvedCap = simplifyCap (capsubst kappa newCapVar)
                                            (posc, T.int32type, T.InternalUsingCap {varName=originalCapVar; cap=resolvedCap}))
                                let collectedUsings = tyUsings @ capUsings
                                let body'' =
                                    match collectedUsings with
                                    | [] ->
                                        // There are no usings to add, so just keep the current body
                                        body'
                                    | _ ->
                                        // Tack on the usings to the start of the function using a SequenceExp
                                        let (pos, tau, _) = body'
                                        let innerBody' = T.SequenceExp (collectedUsings @ [body'])
                                        (pos, tau, innerBody')
                                let closure = Map.empty
                                let funDec' = T.FunctionDec {name=name; template=template; clause={closure=closure; returnTy=retTy'; arguments=arguments'; body=body''}}
                                let accumDtenv'' = Map.add modqual (T.FunDecTy funScheme) accumDtenv'
                                let globalGamma'' = Map.add modqual funScheme accumGlobalGamma'
                                ((module_, funDec'), (accumDtenv'', globalGamma'')))
                            (dtenv, globalGamma)
                    ((funDecs', theta, kappa), (dtenv', globalGamma'))
            ) (dtenv0, globalGammaInit)
    (moduleNames, openDecs, includeDecs, typeDecs, inlineCodeDecs, checkedDecs)