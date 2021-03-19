module Constraint
open TypedAst
open FParsec
open Extensions
open FSharpx.DataStructures
open FSharpx.DataStructures
open FSharpx.DataStructures
open FSharpx.DataStructures

// This code is based off of Norman Ramsey's implementation as
// described in the book Programming Languages: Build, Prove, and Compare

exception TypeError of string

type ErrorMessage = Lazy<string>

type InterfaceConstraint = TyExpr * ConstraintType * ErrorMessage

type Constraint = Equal of TyExpr * TyExpr * ErrorMessage
                | And of Constraint * Constraint
                | InterfaceConstraint of InterfaceConstraint
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
        | (RecordTy (packed, fields)) -> RecordTy (packed, fields |> Map.map (fun _ fieldTau -> subst fieldTau))
    subst

let consubst theta kappa =
    let rec subst =
        function
        | (Equal (tau1, tau2, err)) ->
            Equal (tycapsubst theta kappa tau1, tycapsubst theta kappa tau2, err)
        | (And (c1, c2)) -> And (subst c1, subst c2)
        | Trivial -> Trivial
        | InterfaceConstraint (tau, intConType, err) ->
            InterfaceConstraint (tycapsubst theta kappa tau, intConType, err)
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

let isIntegerType t =
    match t with
    | TyCon (BaseTy b) ->
        match b with
        | (TyUint8 | TyUint16 | TyUint32 | TyUint64 | TyInt8 | TyInt16 | TyInt32 | TyInt64) ->
            true
        | _ ->
            false
    | _ ->
        false

let isRealType t =
    match t with
    | TyCon (BaseTy b) ->
        match b with
        | (TyFloat | TyDouble) ->
            true
        | _ ->
            false
    | _ ->
        false

let isPackedType t =
    match t with
    | RecordTy (Some _, _) ->
        true
    | _ ->
        false

let isRecordType t =
    match t with
    | RecordTy _ ->
        true
    | _ ->
        false

let eqType = (=)

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
        | RecordTy (_, fields) ->
            let (ts, cs) = fields |> Map.values |> Seq.map freeVars |> List.ofSeq |> List.unzip
            (Set.unionMany ts, Set.unionMany cs)
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
    

let instantiate (Forall (formals, caps, constrs, tau)) actuals capActuals =
    let theta = Map.ofList (List.zip formals actuals)
    let kappa = Map.ofList (List.zip caps capActuals)
    (tycapsubst theta kappa tau, constrs |> List.map (fun (tau, conType) -> (tycapsubst theta kappa tau, conType)))

let freshInstance ((Forall (bound, caps, _, _)) as input) =
    let freshTys = List.map freshtyvar bound
    let freshCaps = List.map freshcapvar caps
    (instantiate input freshTys freshCaps, freshTys, freshCaps)

let instantiateRecord (bound, caps, fields) actuals capActuals =
    let substitutions = List.zip bound actuals |> Map.ofList
    let capSubstitutions = List.zip caps capActuals |> Map.ofList
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
    Forall (Set.difference t tyvars |> List.ofSeq, Set.difference c capvars |> List.ofSeq, [], tau)

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

let rec simplifyCap cap =
    match cap with
    | CapacityVar _ -> cap
    | CapacityOp {left=left; op=op; right=right} ->
        let left' = simplifyCap left
        let right' = simplifyCap right
        match (left', right') with
        | (CapacityConst m, CapacityConst n) ->
            match op with
            | CapAdd -> CapacityConst (m + n)
            | CapSubtract -> CapacityConst (m - n)
            | CapMultiply -> CapacityConst (m * n)
            | CapDivide -> CapacityConst (m / n)
        | _ -> 
            CapacityOp {left=left'; op=op; right=right'}
    | CapacityConst _ -> cap
    | CapacityUnaryOp {op=CapNegate; term=term} ->
        let term' = simplifyCap term
        match term' with
        | CapacityConst n -> CapacityConst (-n)
        | _ -> CapacityUnaryOp {op=CapNegate; term=term'}

let rec solveCap con : Map<string, CapacityExpr> =
    match con with
    | TrivialCap -> idSubst
    | AndCap (left, right) ->
        let kappa1 = solveCap left
        let kappa2 = solveCap (consubstCap kappa1 right)
        composeKappa kappa2 kappa1
    | EqualCap (cap, cap', err) ->
        let failMsg = lazy (sprintf "Capacity type error: The capacities %s and %s are not equal.\n\n%s" (capacityString cap) (capacityString cap') (err.Force()))
        match (simplifyCap cap, simplifyCap cap') with
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

let rec simplifyConstraint con =
    match con with
    | And (Trivial, right) ->
        simplifyConstraint right
    | And (left, Trivial) ->
        simplifyConstraint left
    | And (left, right) ->
        match simplifyConstraint left with
        | Trivial -> simplifyConstraint right
        | left' ->
            match simplifyConstraint right with
            | Trivial -> left'
            | right' -> And (left', right')
    | _ ->
        con

let rec constraintTreeToList con =
    match simplifyConstraint con with
    | And (left, right) ->
        List.append (constraintTreeToList left) (constraintTreeToList right)
    | con ->
        [con]

let rec solve con : Map<string, TyExpr> * Map<string, CapacityExpr> * Map<string, (ConstraintType * ErrorMessage) list> =
    match simplifyConstraint con with
    | Trivial -> (Map.empty, Map.empty, Map.empty)
    | con' ->
        let (thetaSolution, capacityConstraints, interfaceConstraints) =
            let rec solveTheta con =
                match con with
                | Trivial -> (idSubst, TrivialCap, [])
                | And (left, right) ->
                    let (theta1, capCon1, intConst1) = solveTheta left
                    let (theta2, capCon2, intConst2) = solveTheta (consubst theta1 Map.empty right)
                    (composeTheta theta2 theta1, AndCap (capCon1, capCon2), List.append intConst1 intConst2)
                | Equal (tau, tau', err) ->
                    let failMsg = lazy (sprintf "Type error: The types %s and %s are not equal.\n\n%s" (typeString tau) (typeString tau') (err.Force()))
                    match (tau, tau') with
                    | ((TyVar a, tau) | (tau, TyVar a)) ->
                        match solveTyvarEq a tau with
                        | Some answer -> (answer, TrivialCap, [])
                        | None -> raise <| TypeError (failMsg.Force())
                    | (TyCon mu, TyCon mu') ->
                        if eqType tau tau' then
                            (idSubst, TrivialCap, [])
                        else
                            raise <| TypeError (failMsg.Force())
                    | (ConApp (t, ts, cs), ConApp(t', ts', cs')) ->
                        if List.length ts = List.length ts' && List.length cs = List.length cs' then
                            let eqAnd c t t' = And (Equal (t, t', err), c)
                            let eqAndCap accum c c' = AndCap (EqualCap (c, c', err), accum)
                            let (theta, capCon1, intConst) = solveTheta (List.fold2 eqAnd Trivial (t::ts) (t'::ts'))
                            let capCon2 = List.fold2 eqAndCap TrivialCap cs cs'
                            (theta, AndCap (capCon1, capCon2), intConst)
                        else
                            raise <| TypeError (failMsg.Force())
                    | (RecordTy (packed, fields), RecordTy (packed', fields')) ->
                        match (packed, packed') with
                        | (Some orderedFields, Some orderedFields') ->
                            if orderedFields = orderedFields' then
                                ()
                            else
                                raise <| TypeError (failMsg.Force())
                        | (None, None) ->
                            ()
                        | _ ->
                            raise <| TypeError (failMsg.Force())
                        if Map.keys fields = Map.keys fields' then
                            let fieldNames = Map.keys fields |> List.ofSeq
                            let getTaus fs = fieldNames |> List.map (fun fieldName -> Map.find fieldName fs)
                            let ts = getTaus fields
                            let ts' = getTaus fields'
                            let fieldConstraints = List.zip ts ts' |> List.map (fun (tau, tau') -> Equal (tau, tau', err)) |> conjoinConstraints
                            solveTheta fieldConstraints
                        else
                            raise <| TypeError (failMsg.Force())
                    | _ -> raise <| TypeError (failMsg.Force())
                | InterfaceConstraint constr ->
                    (idSubst, TrivialCap, [constr])
            solveTheta con'
        let kappaSolution = solveCap capacityConstraints
        let (interfaceConstraintsSolution, extraInterfaceConstraints) =
            interfaceConstraints |>
            List.map
                (fun (tau, constraintType, failMsg) ->
                    let tau' = tycapsubst thetaSolution kappaSolution tau
                    let failMsg' = lazy (sprintf "Interface constraint error: The type %s does not satisfy the %s constraint.\n\n%s" (typeString tau') (interfaceConstraintString constraintType) (failMsg.Force()))
                    match tau' with
                    | TyVar v -> (Some (v, (constraintType, failMsg)), None)
                    | _ ->
                        match constraintType with
                        | IsNum when isNumericalType tau' -> (None, None)
                        | IsInt when isIntegerType tau' -> (None, None)
                        | IsReal when isRealType tau' -> (None, None)
                        | IsPacked when isPackedType tau' -> (None, None)
                        | IsRecord when isRecordType tau' -> (None, None)
                        | HasField (fieldName, fieldTau) ->
                            match tau' with
                            | RecordTy (_, fields) ->
                                match Map.tryFind fieldName fields with
                                | Some recordFieldTau ->
                                    let fieldTau' = tycapsubst thetaSolution kappaSolution fieldTau
                                    (None, Some (recordFieldTau =~= (fieldTau', lazy (sprintf "Record interface constraint error: The concrete type of the field named %s does not match the type of the constraint.\n\n%s" fieldName (failMsg.Force())))))
                                | None ->
                                    raise <| TypeError (sprintf "Record interface constraint error: The concrete record type %s does not contain a field named %s, as required by the record interface constraint.\n\n%s" (typeString tau') fieldName (failMsg.Force()))
                            | _ ->
                                raise <| TypeError (sprintf "Record interface constraint error: The concrete type was determined to be %s, which is not a record. However there is a field constraint, requiring that this type has a field with name %s.\n\n%s" (typeString tau') fieldName (failMsg.Force()))
                        | _ -> raise <| TypeError (failMsg'.Force())) |>
            List.unzip
        let extraInterfaceConstraints' = extraInterfaceConstraints |> List.filter Option.isSome |> List.map Option.get |> conjoinConstraints
        let interfaceConstraintsSolution' = interfaceConstraintsSolution |> List.filter Option.isSome |> List.map Option.get |> Map.ofListDuplicateKeys
        // We now have constraints for each type variable. The next step is to determine if there are any contradictions in the constraints,
        // as well as generate additional constraints for fields with the same name
        let fieldConstraints =
            interfaceConstraintsSolution' |>
            Map.toList |>
            List.map
                (fun (v, constraints) ->
                    constraints |>
                    // Only consider constraints that are HasField
                    List.mapFilter
                        (fun (constr, errMsg) ->
                            match constr with
                            | HasField (fieldName, fieldTau) -> Some (fieldName, (fieldTau, errMsg))
                            | _ -> None) |>
                    // Generate a map where the keys are the field name (in other words group together the constraints by field name)
                    Map.ofListDuplicateKeys |>
                    Map.toList |>
                    List.map
                        (fun (fieldName, (t, errMsg)::taus) ->
                            taus |>
                            List.map
                                (fun (t', errMsg') ->
                                    (t =~= (t', lazy (sprintf "Contradictory record field constraint for field name %s\n\n%s\n\n%s" fieldName (errMsg.Force()) (errMsg'.Force()))))))) |>
            Seq.concat |> // Flatten the constraints generated per type variable
            Seq.concat |> // Flatten the constraints generated per field
            List.ofSeq |>
            conjoinConstraints // Finally conjoin all the constraints together
    
        let newConstraintSystem = extraInterfaceConstraints' &&& fieldConstraints |> simplifyConstraint

        // If there are no further constraints to consider, we have reached a fixed point of the solving process.
        // In this case there is no further information we can gain specifically by considering interface constraints.
        // On the other hand if there are further constraints to consider, then it is possible that solving those constraints
        // will lead to the generation of even more constraints, which we then solve recursively
        match newConstraintSystem with
        | Trivial ->
            (thetaSolution, kappaSolution, interfaceConstraintsSolution')
        | _ ->
            // Generate new InterfaceConstraints to pass to the next invocation of the solver
            let interfaceConstraints' =
                interfaceConstraintsSolution' |>
                Map.toList |>
                List.map
                    (fun (v, constraints) ->
                        // Only pass one field constraint (the first one we find)
                        let fieldConstraints =
                            constraints |>
                            List.mapFilter
                                (fun (constr, errMsg) ->
                                    match constr with
                                    | HasField (fieldName, fieldTau) -> Some (fieldName, (fieldTau, errMsg))
                                    | _ -> None) |>
                            Map.ofListDuplicateKeys |>
                            Map.toList |>
                            List.map
                                (fun (fieldName, (t, errMsg)::_) ->
                                    InterfaceConstraint (TyVar v, HasField (fieldName, t), errMsg))
                        // Pass all other constraints in a passthrough manner
                        let otherConstraints =
                            constraints |>
                            List.filter
                                (fun (constr, _) ->
                                    match constr with
                                    | HasField _ -> false
                                    | _ -> true) |>
                            List.map
                                (fun (constr, errMsg) ->
                                    InterfaceConstraint (TyVar v, constr, errMsg))
                        (conjoinConstraints fieldConstraints) &&& (conjoinConstraints otherConstraints)) |>
                    conjoinConstraints
            let (thetaSolution', kappaSolution', interfaceConstraintsSolution') = solve (newConstraintSystem &&& interfaceConstraints')
            (composeTheta thetaSolution' thetaSolution, composeKappa kappaSolution' kappaSolution, interfaceConstraintsSolution')
        