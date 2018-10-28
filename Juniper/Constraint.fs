module NeoConstraint

// This code is based off of Norman Ramsey's implementation as
// described in the book Programming Languages: Build, Prove, and Compare

open Extensions

exception TypeError of string
exception ImpossibleInternalCompilerError of string
exception InternalCompilerError of string

type ErrorMessage = Lazy<string>

type Namespace = string list
type Kind = Star | KFun of Kind * Kind

let rec kindStack numTyArgs =
    match numTyArgs with
    | 0 -> Star
    | n -> KFun (Star, kindStack (n - 1))

type BaseTyCon = TyConUint8
               | TyConUint16
               | TyConUint32
               | TyConUint64
               | TyConInt8
               | TyConInt16
               | TyConInt32
               | TyConInt64
               | TyConFloat
               | TyConDouble
               | TyConBool
               | TyConUnit
               | TyConPointer
               | TyConString
               | TyConUserDefined of Namespace
               | TyConArray
               | TyConFun
               | TyConFunArgs // TyConFunArgs act a lot like tuples
               | TyConRef
               | TyConTuple

type TyCon = TyCon of BaseTyCon * Kind

type TyVar = TyVar of string * Kind

type TyExpr = TVarExpr of TyVar
            | TConExpr of TyCon
            | TApExpr of TyExpr * TyExpr
//            | TGen of int

[<CustomEquality; CustomComparison>]
type Pred = IsIn of (Namespace * List<TyExpr> * ErrorMessage)
                override x.Equals y =
                    match y with
                    | :? Pred as x' ->
                        let (IsIn (n, t, e), IsIn(n', t', e')) = (x, x')
                        (n, t, e.GetHashCode()) = (n', t', e'.GetHashCode())
                    | _ -> false
                override x.GetHashCode() =
                    let (IsIn (n, t, e)) = x
                    (n, t, e.GetHashCode()).GetHashCode()
                interface System.IComparable with
                    override x.CompareTo y =
                        match y with
                        | :? Pred as x' ->
                            let (IsIn (n, t, e), IsIn(n', t', e')) = (x, x')
                            let tup1 = (n, t, e.GetHashCode())
                            let tup2 = (n', t', e'.GetHashCode())
                            compare tup1 tup2
                        | _ ->
                            invalidArg "y" "Cannot compare Pred to non-Pred type"

type Qual = Qual of (Set<Pred> * TyExpr)
type Inst = Qual
type Class = {superClasses : List<Namespace>; instances : List<Inst>}
type ClassEnv = { classes : Map<Namespace, Class>; defaults : List<TyExpr>}
type Subst = Map<TyVar, TyExpr>
type ConstrainedSubst = (Subst * Set<Pred>)
type Scheme = Forall of (List<TyVar> * Qual)

type Constraint = Equal of Qual * Qual * ErrorMessage
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

let tUint8 = TConExpr (TyCon (TyConUint8, Star))
let tUint16 = TConExpr (TyCon (TyConUint16, Star))
let tUint32 = TConExpr (TyCon (TyConUint32, Star))
let tUint64 = TConExpr (TyCon (TyConUint64, Star))
let tInt8 = TConExpr (TyCon (TyConInt8, Star))
let tInt16 = TConExpr (TyCon (TyConInt16, Star))
let tInt32 = TConExpr (TyCon (TyConInt32, Star))
let tInt64 = TConExpr (TyCon (TyConInt64, Star))
let tFloat = TConExpr (TyCon (TyConFloat, Star))
let tDouble = TConExpr (TyCon (TyConDouble, Star))
let tBool = TConExpr (TyCon (TyConBool, Star))
let tUnit = TConExpr (TyCon (TyConUnit, Star))
let tPointer = TConExpr (TyCon (TyConPointer, Star))
let tString = TConExpr (TyCon (TyConString, Star))

let tArrow = TConExpr (TyCon (TyConFun, KFun (Star, KFun (Star, Star))))
let tFun tArgs tBody = TApExpr (TApExpr (tArrow, tArgs), tBody)

let tFunArgsComma numArgs = TConExpr (TyCon (TyConFunArgs, kindStack numArgs))
let tFunArgs tArgs =
    let numArgs = List.length tArgs
    List.fold (fun accumTyExpr tyArg -> TApExpr (accumTyExpr, tyArg)) (tFunArgsComma numArgs) tArgs

let tComma numArgs = TConExpr (TyCon (TyConTuple, kindStack numArgs))
let tTuple tArgs =
    let numArgs = List.length tArgs
    List.fold (fun accumTyExpr tyArg -> TApExpr (accumTyExpr, tyArg)) (tComma numArgs) tArgs

let tRefCon = TConExpr (TyCon (TyConRef, KFun (Star, Star)))
let tRef refTy = TApExpr (tRefCon, refTy)

let emptyClassEnv = { classes = Map.empty; defaults = [ tInt32; tFloat ] }
let idTheta : Subst = Map.empty
let idSubst : ConstrainedSubst = (idTheta, Set.empty)

let namespaceString (path : Namespace) =
    String.concat ":" path

let baseTyConString b =
    match b with
    | TyConUint8 -> "uint8"
    | TyConUint16 -> "uint16"
    | TyConUint32 -> "uint32"
    | TyConUint64 -> "uint64"
    | TyConInt8 -> "int8"
    | TyConInt16 -> "int16"
    | TyConInt32 -> "int32"
    | TyConInt64 -> "int64"
    | TyConFloat -> "float"
    | TyConDouble -> "double"
    | TyConBool -> "bool"
    | TyConUnit -> "unit"
    | TyConPointer -> "pointer"
    | TyConString -> "string"
    | TyConUserDefined path -> namespaceString path
    // Higher kinded types cannot be printed without context of what they are parameterized by
    | (TyConArray | TyConFun | TyConFunArgs | TyConRef | TyConTuple) ->
        let tyConName =
            match b with
            | TyConArray -> "array"
            | TyConFun -> "function"
            | TyConFunArgs -> "function args"
            | TyConRef -> "ref"
            | TyConTuple -> "tuple"
            | _ -> raise <| ImpossibleInternalCompilerError "Failed to generate type constructor name when generating internal compiler error"
        raise <| InternalCompilerError (sprintf "Cannot convert %s constructor type to string without the context of its type parameters" tyConName)

// * -> * -> * -> * = * -> (* -> (* -> *))
// Flattens an application chain into a list
let rec flattenKindChain k =
    match k with
    | KFun (l, r) ->
        l::(flattenKindChain r)
    | Star ->
        [k]

// let myKind = KFun (Star, KFun (Star, KFun (Star, Star)))
let kindString k =
    let rec kindString' addParens chain =
        let kindString'' addParens k = kindString' addParens (flattenKindChain k)
        let str =
            match chain with
            | [Star] -> "*"
            | _ -> List.map (kindString'' true) chain |> String.concat " -> "
        match chain with
        | [_] -> str
        | _ -> if addParens then sprintf "(%s)" str else str
    kindString' false (flattenKindChain k)

let tyVarString showKind (TyVar (name, kind)) =
    if showKind then
        sprintf "'%s : %s" name (kindString kind)
    else
        sprintf "'%s" name

let tyConString (TyCon (baseTyCon, _)) = baseTyConString baseTyCon

let flattenTypeAppChain e =
    // Example: (((tuple int) bool) float) -> [tuple; int; bool; float]
    let rec flattenTypeArguments' e accum =
        match e with
        | TApExpr (l, r) -> flattenTypeArguments' l (r::accum)
        | _ -> e::accum
    flattenTypeArguments' e []

(*
  TApExpr
    (TApExpr
       (TConExpr (TyCon (TyConTuple,KFun (Star,KFun (Star,Star)))),
        TConExpr (TyCon (TyConBool,Star))),TConExpr (TyCon (TyConUint8,Star)))
*)
let tyExprString e =        
    let rec tyExprString' addParens chain =
        let tyExprString'' addParens e = tyExprString' addParens (flattenTypeAppChain e)
        let str =
            match chain with
            | [(TConExpr (TyCon (TyConRef, _))); containedType] ->
                sprintf "%s ref" (tyExprString'' true containedType)
            | (TConExpr (TyCon (TyConTuple, _)))::tupleArgs ->
                List.map (tyExprString'' true) tupleArgs |> String.concat " * "
            | [(TConExpr (TyCon (TyConArray, _))); containedType; capacityType] ->
                sprintf "%s[%s]" (tyExprString'' true containedType) (tyExprString'' false capacityType)
            | [(TConExpr (TyCon (TyConFun, _))); argsType; (TConExpr (TyCon (TyConFun, _))) as retType] ->
                sprintf "%s -> %s" (tyExprString'' false argsType) (tyExprString'' false retType)
            | [(TConExpr (TyCon (TyConFun, _))); argsType; retType] ->
                sprintf "%s -> %s" (tyExprString'' false argsType) (tyExprString'' true retType)
            | (TConExpr (TyCon (TyConFunArgs, _)))::args ->
                sprintf "(%s)" (List.map (tyExprString'' false) args |> String.concat ", ")
            | (TConExpr (TyCon (baseTy, _)))::args ->
                (baseTyConString baseTy)::(List.map (tyExprString'' true) args) |> String.concat " "
            | TVarExpr tv::args ->
                (tyVarString false tv)::((List.map (tyExprString'' true)) args) |> String.concat " "
            | (TApExpr _)::_ ->
                raise <| InternalCompilerError "Type application was left unflattened"
//            | (TGen _)::_ ->
//                raise <| InternalCompilerError "Attempting to convert TGen to a string"
            | [] ->
                ""
        match chain with
        | [_] -> str
        | _ -> if addParens then sprintf "(%s)" str else str
    tyExprString' false (flattenTypeAppChain e)

let predicateString (IsIn (path, tyExprs, _)) =
    sprintf "%s %s" (namespaceString path) (List.map tyExprString tyExprs |> String.concat " ")

let qualString (Qual (predicates, tau)) =
    let predStr =
        let s = lazy (Set.map predicateString predicates |> String.concat ", ")
        match Set.count predicates with
        | 0 -> ""
        | 1 -> s.Force()
        | _ -> sprintf "(%s)" (s.Force())
    if predStr = "" then
        tyExprString tau
    else
        sprintf "%s => %s" predStr (tyExprString tau)

let classString {superClasses = superClasses; instances = instances} =
    let superClassesStr = List.map namespaceString superClasses |> String.concat ", "
    let instancesStr = List.map qualString instances |> String.concat ", "
    sprintf "Superclasses: %s\nInstances: %s" superClassesStr instancesStr

let classEnvString {classes = classes; defaults = defaults} =
    let classesStr =
        classes |>
        Map.toSeq |>
        Seq.map
            (fun (name, classInfo) ->
                sprintf "Class %s:\n%s" (namespaceString name) (classString classInfo)) |>
        String.concat "\n\n"
    let defaultsStr = List.map tyExprString defaults |> String.concat ", "
    sprintf "%s\n\nDefaults: %s" classesStr defaultsStr

let schemeString (Forall (tyvars, qual)) =
    sprintf "∀ %s . %s" (List.map (tyVarString false) tyvars |> String.concat " ") (qualString qual)

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
//    | TGen _ ->
//        raise <| InternalCompilerError "Attempting to find the kind of a TGen type expression"

let rec tysubst theta t =
    match t with
    | TVarExpr u ->
        match Map.tryFind u theta with
        | Some t' -> t'
        | None -> t
    | TApExpr (l, r) ->
        TApExpr (tysubst theta l, tysubst theta r)
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
        Set.union (freeVarsInTyExpr l) (freeVarsInTyExpr r)
    | TConExpr _ -> Set.empty

let freeVarsInTyExprList ts = List.map freeVarsInTyExpr ts |> Set.unionMany

let freeVarsInPred (IsIn (_, tau, _)) =
    freeVarsInTyExprList tau

let freeVarsInQual (Qual (predicates, tau)) =
    Set.union
        (Set.map freeVarsInPred predicates |> Set.unionMany)
        (freeVarsInTyExpr tau)

let super ({ classes = classes } as classEnv) (path : Namespace) =
    match Map.tryFind path classes with
    | Some { superClasses = superClasses } -> superClasses
    | None -> raise <| InternalCompilerError (sprintf "Attempting to find superclass of typeclass with path %s, but this typeclass does not exist in the passed typeclass environment.\n\nTypeclass environment: %s" (namespaceString path) (classEnvString classEnv))

let insts ({ classes = classes } as classEnv) (path : Namespace) =
    match Map.tryFind path classes with
    | Some { instances = instances } -> instances
    | None -> raise <| InternalCompilerError (sprintf "Attempting to find instances of typeclass with path %s, but this typeclass does not exist in the passed typeclass environment.\n\nTypeclass environment: %s" (namespaceString path) (classEnvString classEnv))

let defined = Option.isSome

let modify ({classes = classes} as env) path classDef =
    {env with classes = Map.add path classDef classes}

// t2(t1(x)) = t2 o t1
// x --> t1 --> t2 -->
let compose ((theta2, preds2) : ConstrainedSubst) ((theta1, preds1) : ConstrainedSubst) : ConstrainedSubst =
    let domain = Set.union (Map.keys theta2) (Map.keys theta1)
    let replaceTheta = (varsubst theta1) >> (tysubst theta2)
    let theta' = Map.fromKeys replaceTheta domain
    let preds' = Set.union (Set.map (predicatesubst theta') preds1) (Set.map (predicatesubst theta') preds2)
    (theta', preds')

let (|--->) (a : TyVar) (tau : TyExpr) (preds : Set<Pred>) =
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

let instantiate (Forall (formals, qual)) actuals =
    qualsubst (Map.ofList (List.zip formals actuals)) qual

let freshInstance (Forall (formals, qual) as scheme) =
    instantiate scheme (List.map (freshtyvar >> TVarExpr) formals)

let generalize skipTyVars qual =
    let ts = freeVarsInQual qual
    Forall (Set.difference ts skipTyVars |> List.ofSeq, qual)

let eqType = (=) : (TyExpr -> TyExpr -> bool)

let solveTyvarEq a tau preds =
    if eqType (TVarExpr a) tau then
        Some idSubst
    elif Set.contains a (freeVarsInTyExpr tau) then
        None // error
    else
        (a |---> tau) preds |> Some

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
            let c = ((Qual (p', l1) =~= Qual (p', l2)) err) &&& ((Qual (p', r1) =~= Qual (p', r2)) err)
            solve c
        | _ ->
            raise <| TypeError (failMsg.Force())