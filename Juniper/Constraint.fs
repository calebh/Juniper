module Constraint
open TypedAst
open FParsec
open Extensions

// This code is based off of Norman Ramsey's implementation as
// described in the book Programming Languages: Build, Prove, and Compare

exception TypeError of string

type ErrorMessage = Lazy<string>
type Constraint = Equal of TyExpr * TyExpr * ErrorMessage
                | And of Constraint * Constraint
                | Trivial

type ConstraintCap = EqualCap of CapacityExpr * CapacityExpr * ErrorMessage
                   | AndCap of ConstraintCap * ConstraintCap
                   | TrivialCap

let (=~=) t1 (t2, err) =
    //printfn "%s =~= %s" (typeString t1) (typeString t2)
    Equal (t1, t2, err)

let (&&&) c1 c2 = And (c1, c2)

let rec conjoinConstraints cc =
    match cc with
    | [] -> Trivial
    | [c] -> c
    | c::cs -> c &&& (conjoinConstraints cs)

let emptyEnv = Map.empty
let idSubst = Map.empty

let bind = Map.add

let rec varsubstCap kappa a =
    match Map.tryFind a kappa with
    | None -> CapacityVar a
    | Some x -> capsubst kappa x

and capsubst kappa =
    function
    | (CapacityVar a) -> varsubstCap kappa a
    | (CapacityOp {op=op; left=left; right=right}) -> CapacityOp {op=op; left=capsubst kappa left; right=capsubst kappa right}
    | (CapacityConst x) -> CapacityConst x
    | (CapacityUnaryOp {op=op; term=term}) -> CapacityUnaryOp {op=op; term=capsubst kappa term}

let rec varsubst theta kappa a =
    match Map.tryFind a theta with
    | None -> TyVar a
    | Some x -> tycapsubst theta kappa x

and tycapsubst theta kappa =
    let rec subst =
        function
        | (TyVar a) -> varsubst theta kappa a
        | (TyCon c) -> TyCon c
        | (ConApp (tau, taus, caps)) -> ConApp (subst tau, List.map subst taus, List.map (capsubst kappa) caps)
    subst

let consubst theta kappa =
    let rec subst =
        function
        | (Equal (tau1, tau2, err)) ->
            Equal (tycapsubst theta kappa tau1, tycapsubst theta kappa tau2, err)
        | (And (c1, c2)) -> And (subst c1, subst c2)
        | Trivial -> Trivial
    subst

let consubstCap kappa =
    let rec subst =
        function
        | (EqualCap (cap1, cap2, err)) ->
            EqualCap (capsubst kappa cap1, capsubst kappa cap2, err)
        | (AndCap (c1, c2)) -> AndCap (subst c1, subst c2)
        | TrivialCap -> TrivialCap
    subst

let isNumericalType t =
    match t with
    | TyCon (BaseTy b) ->
        match b with
        | (TyUint8 | TyUint16 | TyUint32 | TyUint64 | TyInt8 | TyInt16 | TyInt32 | TyInt64 | TyFloat | TyDouble) ->
            true
        | _ ->
            false
    | _ ->
        false

let eqType a b =
    if isNumericalType a && isNumericalType b then
        true
    else
        a = b

let eqCap = (=)

let n = ref 1
let freshtyvar _ =
    let ret = TyVar (sprintf "t%i" !n)
    n := !n + 1
    ret

let n2 = ref 1
let freshcapvar _ =
    let ret = CapacityVar (sprintf "c%i" !n2)
    n2 := !n2 + 1
    ret

// f(g(x)) = f o g
// x --> g --> f -->
let composeTheta f g =
    let xs = Set.union (Map.keys f) (Map.keys g)
    xs |> Set.fold (fun accumMap x ->
        accumMap |>
        Map.add
            x
            (match Map.tryFind x g with
            | Some (TyVar x') ->
                match Map.tryFind x' f with
                | Some f_of_g_of_x ->
                    f_of_g_of_x
                | None ->
                    TyVar x'
            | Some g_of_x ->
                g_of_x
            | None ->
                match Map.tryFind x f with
                | Some f_of_x ->
                    f_of_x
                | None ->
                    TyVar x)
    ) Map.empty

let composeKappa f g =
    let xs = Set.union (Map.keys f) (Map.keys g)
    xs |> Set.fold (fun accumMap x ->
        accumMap |>
        Map.add
            x
            (match Map.tryFind x g with
            | Some (CapacityVar x') ->
                match Map.tryFind x' f with
                | Some f_of_g_of_x ->
                    f_of_g_of_x
                | None ->
                    CapacityVar x'
            | Some g_of_x ->
                g_of_x
            | None ->
                match Map.tryFind x f with
                | Some f_of_x ->
                    f_of_x
                | None ->
                    CapacityVar x)
    ) Map.empty

let rec freeCapVars =
    function
    | CapacityVar name -> Set.singleton name
    | CapacityOp {left=left; right=right} -> Set.union (freeCapVars left) (freeCapVars right)
    | CapacityConst _ -> Set.empty
    | CapacityUnaryOp {term=term} -> freeCapVars term

let rec freeVars t =
    let rec freeTyVars =
        function 
        | TyVar v -> (Set.singleton v, Set.empty)
        | TyCon _ -> (Set.empty, Set.empty)
        | ConApp (ty, tys, caps) ->
            let (ts, c1) = List.map freeVars (ty::tys) |> List.unzip
            let c2 = List.map freeCapVars caps
            (Set.unionMany ts, Set.union (Set.unionMany c1) (Set.unionMany c2))
    freeTyVars t

let freeTyVars t =
    freeVars t |> fst

let (|--->) a tau =
    match tau with
    | TyVar a' -> if a = a' then idSubst else bind a tau emptyEnv
    | _ ->
        if Set.contains a (freeTyVars tau) then
            failwith "non-idemptotent substitution"
        else
            bind a tau emptyEnv

let (|-%->) a cap =
    match cap with
    | CapacityVar a' -> if a = a' then idSubst else bind a cap emptyEnv
    | _ ->
        if Set.contains a (freeCapVars cap) then
            failwith "non-idemptotent capacity substitution"
        else
            bind a cap emptyEnv
    

let instantiate (Forall (formals, caps, tau)) actuals capActuals =
    tycapsubst (Map.ofList (List.zip formals actuals)) (Map.ofList (List.zip caps capActuals)) tau

let freshInstance (Forall (bound, caps, tau)) =
    let freshTys = List.map freshtyvar bound
    let freshCaps = List.map freshcapvar caps
    (instantiate (Forall (bound, caps, tau)) freshTys freshCaps, freshTys, freshCaps)

let instantiateRecord (bound, caps, fields) actuals capActuals =
    let substitutions = List.zip bound actuals |> Map.ofList
    let capSubstitutions = List.zip bound capActuals |> Map.ofList
    fields |> Map.map (fun (fieldName : string) tau -> tycapsubst substitutions capSubstitutions tau)

let freshInstanceRecord (bound, caps, fields) =
    instantiateRecord (bound, caps, fields) (List.map freshtyvar bound) (List.map freshcapvar caps)

(*
let canonicalize (Forall (bound, ty)) =
    let canonicalTyvarName n =
        let letters = "abcdefghijklmnopqrstuvwxyz"
        if n < 26 then
            sprintf "%c" letters.[n]
        else
            sprintf "v%i" (n - 25)
    let free = Set.difference (freeTyVars ty) (Set.ofSeq bound)
    let rec unusedIndex n =
        if Set.contains (canonicalTyvarName n) free then
           unusedIndex (n+1)
        else
            n
    let rec newBoundVars =
        function
        | (_, []) -> []
        | (index, oldvar::oldvars) ->
            let n = unusedIndex index
            (canonicalTyvarName n) :: (newBoundVars (n+1, oldvars))
    let newBound = newBoundVars (0, bound)
    Forall (newBound, tysubst (Map.ofList (List.zip bound (List.map TyVar newBound))) ty)
*)

let generalize tyvars capvars tau =
    let (t, c) = freeVars tau
    Forall (Set.difference t tyvars |> List.ofSeq, Set.difference c capvars |> List.ofSeq, tau)

let solveTyvarEq a tau =
    if eqType (TyVar a) tau then
        Some idSubst
    elif Set.contains a (freeTyVars tau) then
        None // error
    else
        a |---> tau |> Some

let solveCapvarEq a cap =
    if eqCap (CapacityVar a) cap then
        Some idSubst
    elif Set.contains a (freeCapVars cap) then
        None
    else
        a |-%-> cap |> Some

let rec solveCap con : Map<string, CapacityExpr> =
    match con with
    | TrivialCap -> idSubst
    | AndCap (left, right) ->
        let kappa1 = solveCap left
        let kappa2 = solveCap (consubstCap kappa1 right)
        composeKappa kappa2 kappa1
    | EqualCap (cap, cap', err) ->
        let failMsg = lazy (sprintf "Capacity type error: The capacities %s and %s are not equal.\n\n%s" (capacityString cap) (capacityString cap') (err.Force()))
        match (cap, cap') with
        | ((CapacityVar a, cap) | (cap, CapacityVar a)) ->
            match solveCapvarEq a cap with
            | Some answer -> answer
            | None -> raise <| TypeError (failMsg.Force())
        | (CapacityConst a, CapacityConst b) ->
            if a = b then
                idSubst
            else
                raise <| TypeError (failMsg.Force())
        | (CapacityOp {left=left; op=op; right=right}, CapacityOp {left=left'; op=op'; right=right'}) when op = op' ->
            solveCap (AndCap (EqualCap (left, left', err), EqualCap (right, right', err)))
        | (CapacityUnaryOp {term=term; op=op}, CapacityUnaryOp {term=term'; op=op'}) when op = op' ->
            solveCap (EqualCap (term, term', err))
        | _ ->
            raise <| TypeError (failMsg.Force())
            

let solve con : Map<string, TyExpr> * Map<string, CapacityExpr> =
    let (thetaSolution, capacityConstraints) =
        let rec solveTheta con =
            match con with
            | Trivial -> (idSubst, TrivialCap)
            | And (left, right) ->
                let (theta1, capCon1) = solveTheta left
                let (theta2, capCon2) = solveTheta (consubst theta1 Map.empty right)
                (composeTheta theta2 theta1, AndCap (capCon1, capCon2))
            | Equal (tau, tau', err) ->
                let failMsg = lazy (sprintf "Type error: The types %s and %s are not equal.\n\n%s" (typeString tau) (typeString tau') (err.Force()))
                match (tau, tau') with
                | ((TyVar a, tau) | (tau, TyVar a)) ->
                    match solveTyvarEq a tau with
                    | Some answer -> (answer, TrivialCap)
                    | None -> raise <| TypeError (failMsg.Force())
                | (TyCon mu, TyCon mu') ->
                    if eqType tau tau' then
                        (idSubst, TrivialCap)
                    else
                        raise <| TypeError (failMsg.Force())
                | (ConApp (t, ts, cs), ConApp(t', ts', cs')) ->
                    if List.length ts = List.length ts' && List.length cs = List.length cs' then
                        let eqAnd c t t' = And (Equal (t, t', err), c)
                        let eqAndCap accum c c' = AndCap (EqualCap (c, c', err), accum)
                        let (theta, capCon1) = solveTheta (List.fold2 eqAnd Trivial (t::ts) (t'::ts'))
                        let capCon2 = List.fold2 eqAndCap TrivialCap cs cs'
                        (theta, AndCap (capCon1, capCon2))
                    else
                        raise <| TypeError (failMsg.Force())
                | _ -> raise <| TypeError (failMsg.Force())
        solveTheta con
    let kappaSolution = solveCap capacityConstraints
    (thetaSolution, kappaSolution)