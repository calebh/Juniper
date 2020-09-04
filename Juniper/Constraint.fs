module Constraint
open Error
open TypedAst

// This code is based off of Norman Ramsey's implementation as
// described in the book Programming Languages: Build, Prove, and Compare

open Extensions

type ErrorMessage = Lazy<string>

type Constraint = Equal of Qual<TyExpr, TyExpr> * Qual<TyExpr, TyExpr> * ErrorMessage
                | And of Constraint * Constraint
                | Trivial

let (=~=) q1 q2 err = Equal (q1, q2, err)

let (&&&) c1 c2 = And (c1, c2)

let rec conjoinConstraints cc =
    match cc with
    | [] -> Trivial
    | [c] -> c
    | c::cs -> c &&& (conjoinConstraints cs)

let n = ref 1

let freshpolytyvar kind =
    let ret = TyVar (sprintf "t%i" !n, kind)
    n := !n + 1
    ret

let freshtyvar _ =
    freshpolytyvar Star

let emptyClassEnv = Map.empty
let idTheta : Subst = Map.empty
let idSubst : ConstrainedSubst = (idTheta, Set.empty)

let kindOfTyVar (TyVar (_, k)) = k
let kindOfTyCon (TyCon (_, k)) = k
let rec kindOfTyExpr tau =
    match tau with
    | TVarExpr t -> kindOfTyVar t
    | TConExpr t -> kindOfTyCon t
    | TApExpr (t, _) ->
        match kindOfTyExpr t with
        | KFun (_, k) -> k
        | _ -> raise <| InternalCompilerError "Invalid kind was encountered when attempting to determine the kind of a TApExpr"

let rec tysubst theta t =
    match t with
    | TVarExpr u ->
        match Map.tryFind u theta with
        | Some t' -> t'
        | None -> t
    | TApExpr (l, r) ->
        TApExpr (tysubst theta l, List.map (tysubst theta) r)
    | _ ->
        t

let varsubst (theta : Subst) (v : TyVar) =
    match Map.tryFind v theta with
    | Some tau -> tau
    | None -> TVarExpr v

let tyssubst s ts = List.map (tysubst s) ts

let predicatesubst s (IsIn (path, taus, err)) =
    IsIn (path, tyssubst s taus, err)

let qualsubst s (Qual (predicates, tau)) =
    Qual (Set.map (predicatesubst s) predicates, (tysubst s tau))

let schemesubst s (Forall (ks, qt)) =
    Forall (ks, qualsubst s qt)

let rec freeVarsInTyExpr t =
    match t with
    | TVarExpr u -> Set.singleton u
    | TApExpr (l, r) ->
        Set.union (freeVarsInTyExpr l) (List.map freeVarsInTyExpr r |> Set.unionMany)
    | TConExpr _ -> Set.empty

let freeVarsInTyExprList ts = List.map freeVarsInTyExpr ts |> Set.unionMany

let freeVarsInPred (IsIn (_, tau, _)) =
    freeVarsInTyExprList tau

let freeVarsInQual (Qual (predicates, tau)) =
    Set.union
        (Set.map freeVarsInPred predicates |> Set.unionMany)
        (freeVarsInTyExpr tau)

let super classes modQual =
    match Map.tryFind modQual classes with
    | Some (Qual (superClasses, _)) -> superClasses
    | None -> raise <| InternalCompilerError (sprintf "Attempting to find superclass of typeclass with path %s, but this typeclass does not exist in the passed typeclass environment.\n\nTypeclass environment: %s" (modQualifierString modQual) (classEnvString classes))

let defined = Option.isSome

let modify classes path classDef =
    Map.add path classDef classes

// t2(t1(x)) = t2 o t1
// x --> t1 --> t2 -->
let compose ((theta2, preds2) : ConstrainedSubst) ((theta1, preds1) : ConstrainedSubst) : ConstrainedSubst =
    let domain = Set.union (Map.keys theta2) (Map.keys theta1)
    let replaceTheta = (varsubst theta1) >> (tysubst theta2)
    let theta' = Map.fromKeys replaceTheta domain
    let preds' = Set.union (Set.map (predicatesubst theta') preds1) (Set.map (predicatesubst theta') preds2)
    (theta', preds')

let (|--->) (a : TyVar) (tau : TyExpr) (preds : Set<Pred<TyExpr>>) =
    let theta =
        match tau with
        | TVarExpr tv ->
            if tv = a then idTheta else Map.singleton a tau
        | _ ->
            if Set.contains a (freeVarsInTyExpr tau) then
                raise <| InternalCompilerError "non-idempotent substitution"
            else
                Map.singleton a tau
    let preds' = Set.map (predicatesubst theta) preds
    (theta, preds')

let instantiate (Forall (formals, qual)) (actualQuals : List<Qual<TyExpr, TyExpr>>) =
    let actualsPreds = List.map getQualPreds actualQuals |> Set.unionMany
    let actuals = List.map unwrapQual actualQuals
    let (Qual (preds', tau)) = qualsubst (Map.ofList (List.zip formals actuals)) qual
    Qual (Set.union actualsPreds preds', tau)

let freshInstance (Forall (formals, _) as scheme) =
    let actuals = List.map (freshtyvar >> TVarExpr >> fun tau -> Qual (Set.empty, tau)) formals
    (instantiate scheme actuals, actuals)

let generalize skipTyVars qual =
    let ts = freeVarsInQual qual
    Forall (Set.difference ts skipTyVars |> List.ofSeq, qual)

let eqType = (=) : (TyExpr -> TyExpr -> bool)

let kindOf (tau : TyExpr) : Kind =
    match tau with
    | TVarExpr (TyVar (_, kind)) -> kind
    | TApExpr _ -> Star
    | TConExpr (TyCon (_, kind)) -> kind

let solveTyvarEq a tau preds =
    if eqType (TVarExpr a) tau then
        Some idSubst
    elif Set.contains a (freeVarsInTyExpr tau) then
        None // error
    else
        if (kindOf (TVarExpr a)) = (kindOf tau) then
            (a |---> tau) preds |> Some
        else
            None

let rec consubst theta con =
    match con with
    | Equal (Qual (preds1, tau1), Qual (preds2, tau2), err) ->
        let ts = tysubst theta
        let ps = Set.map (predicatesubst theta)
        Equal (Qual (ps preds1, ts tau1), Qual (ps preds2, ts tau2), err)
    | And (c1, c2) ->
        And (consubst theta c1, consubst theta c2)
    | Trivial ->
        Trivial

let rec solve con : ConstrainedSubst =
    match con with
    | Trivial -> idSubst
    | And (left, right) ->
        let ((theta1, preds1) as s1) = solve left
        let ((theta2, preds2) as s2) = solve (consubst theta1 right)
        compose s2 s1
    | Equal (Qual (preds1, tau1), Qual (preds2, tau2), err) ->
        let failMsg = lazy (sprintf "Type error: The types %s and %s are not equal.\n\n%s" (tyExprString tau1) (tyExprString tau2) (err.Force()))
        let preds' = lazy (Set.union preds1 preds2)
        match (tau1, tau2) with
        | ((TVarExpr a, tau') | (tau', TVarExpr a)) ->
            match solveTyvarEq a tau' (preds'.Force()) with
            | Some answer -> answer
            | None -> raise <| TypeError (failMsg.Force())
        | (TConExpr mu1, TConExpr mu2) ->
            if mu1 = mu2 then
                (Map.empty, preds'.Force())
            else
                raise <| TypeError (failMsg.Force())
        | (TApExpr (l1, r1), TApExpr (l2, r2)) ->
            let p' = preds'.Force()
            let c1 = (Qual (p', l1) =~= Qual (p', l2)) err
            if List.length r1 = List.length r2 then
                let c2 = List.zip r1 r2 |> List.map (fun (tau1, tau2) -> ((Qual (p', tau1) =~= Qual (p', tau2)) err)) |> conjoinConstraints
                let c = c1 &&& c2
                solve c
            else
                raise <| TypeError (failMsg.Force())
        | _ ->
            raise <| TypeError (failMsg.Force())

let isOverlapping ((Qual (_, IsIn (name1, tyExprs1, _))) : Inst) (Qual (_, IsIn (name2, tyExprs2, _)) : Inst) =
    if name1 = name2 then
        let c = conjoinConstraints (List.zip tyExprs1 tyExprs2 |> List.map (fun (tau1, tau2) -> (Qual (Set.empty, tau1) =~= Qual (Set.empty, tau2)) (lazy "")))
        try
            solve c |> ignore
            true
        with
        | TypeError _ -> false
    else
        raise <| InternalCompilerError "Checking overlapping instances between instances of two different typeclasses"
