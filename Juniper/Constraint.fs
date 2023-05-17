module Constraint
open TypedAst
open Extensions
open Symbolism.EliminateVariable
open Symbolism.SimplifyEquation
open Symbolism.IsolateVariable
open Symbolism.Has
open Symbolism.SimplifyLogical

// This code is based off of Norman Ramsey's implementation as
// described in the book Programming Languages: Build, Prove, and Compare

exception TypeError of List<Error.ErrStr>

type ErrorMessage = Lazy<List<Error.ErrStr>>

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
        | (ClosureTy fields) -> ClosureTy (fields |> Map.map (fun _ fieldTau -> subst fieldTau))
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
        | ClosureTy fields ->
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

let generalize tyvars capvars (interfaceConstraints : Map<string, ConstraintType list>) tau =
    let (t, c) = freeVars tau
    let interfaceConstraints' =
        t |>
        Set.map
            (fun tau ->
                match Map.tryFind tau interfaceConstraints with
                | Some constraints ->
                    constraints |>
                    List.map (fun constTyp -> (TyVar tau, constTyp))
                | None -> []) |>
        Seq.concat |>
        List.ofSeq
    Forall (Set.difference t tyvars |> List.ofSeq, Set.difference c capvars |> List.ofSeq, interfaceConstraints', tau)

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

(*
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
*)

(*
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
*)

exception EquationConversionError of string

let rec constraintCapTreeToList con =
    match con with
    | AndCap (left, right) ->
        List.append (constraintCapTreeToList left) (constraintCapTreeToList right)
    | TrivialCap ->
        []
    | EqualCap _ as con ->
        [con]

let numDenomToFrac numerator denominator =
    match (numerator, denominator) with
    | (_::_, []) ->
        numerator |> List.reduce (fun accumExpr element -> CapacityOp {left=accumExpr; op=CapMultiply; right=element})
    | ([], _::_) ->
        let denominator' = denominator |> List.reduce (fun accumExpr element -> CapacityOp {left=accumExpr; op=CapMultiply; right=element})
        CapacityOp {left=CapacityConst 1L; op=CapDivide; right=denominator'}
    | (_::_, _::_) ->
        let numerator' = numerator |> List.reduce (fun accumExpr element -> CapacityOp {left=accumExpr; op=CapMultiply; right=element})
        let denominator' = denominator |> List.reduce (fun accumExpr element -> CapacityOp {left=accumExpr; op=CapMultiply; right=element})
        CapacityOp {left=numerator'; op=CapDivide; right=denominator'}
    | ([], []) ->
        CapacityConst 1L

let rec symbolismMathObjToCapExpr (m : Symbolism.MathObject) =
    match m with
    | :? Symbolism.Sum as sum ->
        sum.elts |>
        List.ofSeq |>
        List.map symbolismMathObjToCapExpr |>
        List.reduce
            (fun accumExpr element -> CapacityOp {left=accumExpr; op=CapAdd; right=element})
    | :? Symbolism.Product as prd ->
        let (numerator, denominator) =
            prd.elts |>
            List.ofSeq |>
            Seq.fold
                (fun (numerator, denominator) element ->
                    match element with
                    | :? Symbolism.Power as pwr ->
                        match symbolismMathObjToCapExpr (pwr.exp) with
                        | CapacityConst c ->
                            if c < 0L then
                                if c = -1L then
                                    (numerator, (symbolismMathObjToCapExpr pwr.bas)::denominator)
                                else
                                    let bas' = symbolismMathObjToCapExpr pwr.bas
                                    (numerator, List.append (List.replicate (int(-c)) bas') denominator)
                            else
                                if c = 1L then
                                    ((symbolismMathObjToCapExpr pwr.bas)::numerator, denominator)
                                elif c = 0L then
                                    (numerator, denominator)
                                else
                                    let bas' = symbolismMathObjToCapExpr pwr.bas
                                    (List.append (List.replicate (int(c)) bas') numerator, denominator)
                        | _ ->
                            raise (EquationConversionError("Non-numerical exponent"))
                    | _ ->
                        ((symbolismMathObjToCapExpr element)::numerator, denominator))
                ([], [])
        numDenomToFrac numerator denominator
    | :? Symbolism.Fraction as frac ->
        CapacityOp {left=(symbolismMathObjToCapExpr (frac.Numerator())); op=CapDivide; right=(symbolismMathObjToCapExpr (frac.Denominator()))}
    | :? Symbolism.Integer as i ->
        CapacityConst (int64(i.``val``))
    | :? Symbolism.Symbol as sym ->
        CapacityVar (sym.name)
    | :? Symbolism.Power as pwr ->
        let (numerator, denominator) =
            match symbolismMathObjToCapExpr (pwr.exp) with
            | CapacityConst c ->
                let bas' = symbolismMathObjToCapExpr pwr.bas
                if c < 0L then
                    ([], List.replicate (int(-c)) bas')
                else
                    (List.replicate (int(c)) bas', [])
            | _ ->
                raise (EquationConversionError("Non-numerical exponent"))
        numDenomToFrac numerator denominator
    | _ ->
        raise (EquationConversionError("Unknown or incompatibile Symbolism equation type"))

let rec simplifyCap (cap : CapacityExpr) : CapacityExpr =
    let varNames = cap |> freeCapVars |> List.ofSeq
    let varSymbols = varNames |> List.map (fun varName -> new Symbolism.Symbol(varName))
    let namesToSymbol = List.zip varNames varSymbols |> Map.ofList
    let rec internalSimplify (cap : CapacityExpr) =
        match cap with
        | CapacityVar v ->
            ((Map.find v namesToSymbol) :> Symbolism.MathObject)
        | CapacityOp {left=left; op=op; right=right} ->
            let left' = internalSimplify left
            let right' = internalSimplify right
            match op with
            | CapAdd ->
                left' + right'
            | CapSubtract ->
                left' - right'
            | CapMultiply ->
                left' * right'
            | CapDivide ->
                left' / right'
        | CapacityUnaryOp {term=term; op=CapNegate} ->
            -(internalSimplify term)
        | CapacityConst a ->
            (new Symbolism.Integer(int32(a))) :> Symbolism.MathObject
    let symbolismRepresentation = internalSimplify cap
    let simplifiedRepresentation = symbolismRepresentation.SimplifyEquation()
    symbolismMathObjToCapExpr simplifiedRepresentation

let rec capacityExprContainsVar varName expr =
    match expr with
    | CapacityVar v ->
        v = varName
    | CapacityOp {left=left; right=right} ->
        (capacityExprContainsVar varName left) || (capacityExprContainsVar varName right)
    | CapacityUnaryOp {term=term} ->
        capacityExprContainsVar varName term
    | CapacityConst _ ->
        false

let solveCap (con : ConstraintCap) (terminalCaps : string list) : Map<string, CapacityExpr> =
    let con' = constraintCapTreeToList con
    let varNamesSet = con' |> List.map (fun (EqualCap (left, right, _)) -> Set.union (freeCapVars left) (freeCapVars right)) |> Set.unionMany
    let terminalCapsSet = Set.ofList terminalCaps
    // Convert varNamesSet to a list, such that terminalCaps are at the very end of the list
    let varNames = List.append (List.ofSeq (Set.difference varNamesSet terminalCapsSet)) (List.ofSeq (Set.intersect varNamesSet terminalCapsSet))
    let relevantEquations varName = con' |> List.filter (fun (EqualCap (left, right, _)) -> (capacityExprContainsVar varName left) || (capacityExprContainsVar varName right))
    let varSymbols = varNames |> List.map (fun varName -> new Symbolism.Symbol(varName))
    let namesToSymbol = List.zip varNames varSymbols |> Map.ofList
    let rec capExprToSymbolismExpr cap : Symbolism.MathObject =
        match cap with
        | CapacityVar v ->
            ((Map.find v namesToSymbol) :> Symbolism.MathObject)
        | CapacityOp {left=left; op=op; right=right} ->
            let left' = capExprToSymbolismExpr left
            let right' = capExprToSymbolismExpr right
            match op with
            | CapAdd ->
                left' + right'
            | CapSubtract ->
                left' - right'
            | CapMultiply ->
                left' * right'
            | CapDivide ->
                left' / right'
        | CapacityUnaryOp {term=term; op=CapNegate} ->
            -(capExprToSymbolismExpr term)
        | CapacityConst a ->
            (new Symbolism.Integer(int32(a))) :> Symbolism.MathObject
    let symbolismSystemOfEq = con' |> List.map (fun (EqualCap (left, right, _)) -> (new Symbolism.Equation((capExprToSymbolismExpr left), (capExprToSymbolismExpr right))) :> Symbolism.MathObject)
    let dummySymbol = new Symbolism.Symbol("dummy")
    // The need for this dummy equation is a bit obscure. Basically if the solver eliminates all the variables from the system of equations
    // using the EliminateVariables method, it throws an exception. This dummy equation will ensure that eliminatedSystem will never
    // be empty. The equation dummy == dummy will end up being converted to Symbolism.Bool(true) by the SymbolismExt.heuristicSimplify method
    let dummyEquation = new Symbolism.Equation(dummySymbol, dummySymbol) :> Symbolism.MathObject
    let symbolismEq = new Symbolism.And((dummyEquation::symbolismSystemOfEq) |> Array.ofList)
    varSymbols |>
    List.fold
        (fun (env, symbolsSolvedSoFar) sym ->
            let relevantErrors = lazy (relevantEquations sym.name |> List.map (fun (EqualCap (left, right, err)) -> err.Force()) |> List.concat)
            // Todo: try catch for EliminateVariables and IsolateVariable
            try
                let eliminatedSystem = symbolismEq.EliminateVariables(symbolsSolvedSoFar |> Array.ofList)
                match eliminatedSystem with
                | :? Symbolism.Bool as b ->
                    if b.``val`` then
                        (env, symbolsSolvedSoFar)
                    else
                        raise <|
                            TypeError
                                ([Error.ErrMsg (sprintf "Error when solving the system of equations for the solution of %s. The system of equations is insolvable. Relevant capacity constraints which led to this situation are:" sym.name)]
                                @
                                (relevantErrors.Force())
                                @
                                ([Error.ErrMsg (sprintf "The system of equations is the following: %s\n\nWhen isolated and solve this resulted in the following system of equations: %s" (symbolismEq.ToString()) (eliminatedSystem.ToString()))]))
                | _ ->
                    let solvedSystem = eliminatedSystem.IsolateVariable(sym).SimplifyLogical() |> SymbolismExt.heuristicSimplify
                    match solvedSystem with
                    | :? Symbolism.Bool as b ->
                        if b.``val`` then
                            (env, symbolsSolvedSoFar)
                        else
                            raise <|
                                TypeError
                                    ([Error.ErrMsg (sprintf "Error when solving the system of equations for the solution of %s. The system of equations is insolvable. Relevant capacity constraints which led to this situation are:" sym.name)]
                                    @
                                    relevantErrors.Force()
                                    @
                                    ([Error.ErrMsg (sprintf "The system of equations is the following: %s\n\nWhen isolated and solve this resulted in the following system of equations: %s" (symbolismEq.ToString()) (solvedSystem.ToString()))]))
                    | _ ->
                        match SymbolismExt.extractSolution solvedSystem sym with
                        | Some solution ->
                            try
                                let solutionCap = symbolismMathObjToCapExpr solution
                                let env' = Map.add sym.name solutionCap env
                                (env', sym::symbolsSolvedSoFar)
                            with
                            | :? EquationConversionError ->
                                raise <|
                                    TypeError
                                        ([Error.ErrMsg (sprintf "Error when converting the equation for the solution of %s. The solution could not be written in terms of basic arithmetic operations. Relevant capacity constraints which led to this solution are:" sym.name)]
                                        @
                                        relevantErrors.Force()
                                        @
                                        ([Error.ErrMsg (sprintf "The system of equations is the following: %s\n\nWhen isolated and solve this resulted in the following system of equations: %s" (symbolismEq.ToString()) (solvedSystem.ToString()))]))
                        | None ->
                            if solvedSystem.Has(sym) then
                                raise <|
                                    TypeError
                                        ([Error.ErrMsg (sprintf "Unable to extract solution from the system of equations for %s. Relevant capacity constraints which led to this situation are:" sym.name)]
                                        @
                                        relevantErrors.Force()
                                        @
                                        ([Error.ErrMsg (sprintf "The system of equations is the following: %s.\n\nWhen isolated and solve this resulted in the following system of equations: %s" (symbolismEq.ToString()) (solvedSystem.ToString()))]))
                            else
                                (env, symbolsSolvedSoFar)
                with
                | :? System.Exception as exc ->
                    raise <| TypeError [Error.ErrMsg (sprintf "An exception was thrown while eliminating variables or isolating them when running the capacity solver system. The exception was: %s" (exc.ToString()))])
        (Map.empty, []) |>
    fst

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

// con is the constraint system we would like to solve. terminalCaps is a bit harder to explain. They are the
// the capacity variables that we would like the other capacity variables to be written in terms of. Therefore
// they are the last capacity variables that should be solved for (and therefore eliminated) in the Symbolism
// equation solving process
let rec solve (con : Constraint) (terminalCaps : string list) : Map<string, TyExpr> * Map<string, CapacityExpr> * Map<string, (ConstraintType * ErrorMessage) list> =
    let rec innerSolve (con : Constraint) : Map<string, TyExpr> * ConstraintCap * Map<string, (ConstraintType * ErrorMessage) list> =
        match simplifyConstraint con with
        | Trivial -> (Map.empty, TrivialCap, Map.empty)
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
                        let failMsg = lazy ([Error.ErrMsg (sprintf "Type error: The types %s and %s are not equal." (typeString tau) (typeString tau'))] @ err.Force())
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
                        | (ClosureTy fields, ClosureTy fields') ->
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
            let (interfaceConstraintsSolution, extraInterfaceConstraints) =
                interfaceConstraints |>
                List.map
                    (fun (tau, constraintType, failMsg) ->
                        let tau' = tycapsubst thetaSolution Map.empty tau
                        let failMsg' = lazy ([Error.ErrMsg (sprintf "Interface constraint error: The type %s does not satisfy the %s constraint." (typeString tau') (interfaceConstraintString constraintType))] @ failMsg.Force())
                        match tau' with
                        | TyVar v ->
                            let constraintType' =
                                match constraintType with
                                | HasField (fieldName, fieldTau) ->
                                    HasField (fieldName, tycapsubst thetaSolution Map.empty fieldTau)
                                | _ ->
                                    constraintType
                            (Some (v, (constraintType', failMsg)), None)
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
                                        let fieldTau' = tycapsubst thetaSolution Map.empty fieldTau
                                        (None, Some (recordFieldTau =~= (fieldTau', lazy ([Error.ErrMsg (sprintf "Record interface constraint error: The concrete type of the field named %s does not match the type of the constraint." fieldName)] @ failMsg.Force()))))
                                    | None ->
                                        raise <| TypeError ([Error.ErrMsg (sprintf "Record interface constraint error: The concrete record type %s does not contain a field named %s, as required by the record interface constraint." (typeString tau') fieldName)] @ failMsg.Force())
                                | _ ->
                                    raise <| TypeError ([Error.ErrMsg (sprintf "Record interface constraint error: The concrete type was determined to be %s, which is not a record. However there is a field constraint, requiring that this type has a field with name %s." (typeString tau') fieldName)] @ failMsg.Force())
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
                                        (t =~= (t', lazy ([Error.ErrMsg (sprintf "Contradictory record field constraint for field name %s" fieldName)] @ errMsg.Force() @ errMsg'.Force())))))) |>
                Seq.concat |> // Flatten the constraints generated per type variable
                Seq.concat |> // Flatten the constraints generated per field
                List.ofSeq |>
                conjoinConstraints // Finally conjoin all the constraints together
    
            let newConstraintSystem = (extraInterfaceConstraints' &&& fieldConstraints) |> simplifyConstraint

            // If there are no further constraints to consider, we have reached a fixed point of the solving process.
            // In this case there is no further information we can gain specifically by considering interface constraints.
            // On the other hand if there are further constraints to consider, then it is possible that solving those constraints
            // will lead to the generation of even more constraints, which we then solve recursively
            match newConstraintSystem with
            | Trivial ->
                (thetaSolution, capacityConstraints, interfaceConstraintsSolution')
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
                let (thetaSolution', capacityConstraints', interfaceConstraintsSolution') = innerSolve (newConstraintSystem &&& interfaceConstraints')
                (composeTheta thetaSolution' thetaSolution, AndCap (capacityConstraints, capacityConstraints'), interfaceConstraintsSolution')
    let (thetaSolution, capacityConstraints, interfaceConstraintsSolution) = innerSolve con
    let kappaSolution = solveCap capacityConstraints terminalCaps
    (thetaSolution, kappaSolution, interfaceConstraintsSolution)
        