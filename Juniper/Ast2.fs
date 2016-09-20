module Ast2
open FParsec

// Allows for module type to be used for declaring modules.
type Module = Module of PosAdorn<Declaration> list

// Tuple of starting position and ending position
// Note: The 'option' keyword indicates that field is optional (can have 'none' as assignment)

// PosAdorn wraps a an AST object in a start and end line position for helpful debugging
// messages. It also includes the type of the object, which starts as 'none'.
// Virtually every object in the AST is a PosAdorn wrapping another object.
and PosAdorn<'a> = (Position * Position) * 'a

// Top level declarations
// Function object. Template is optional.
and FunctionRec = { name     : PosAdorn<string>;
                    template : PosAdorn<Template> option;
                    clause   : PosAdorn<FunctionClause> }

// Record object. Template is optional.
and RecordRec =   { name     : PosAdorn<string>;
                    fields   : PosAdorn<(PosAdorn<string> * PosAdorn<TyExpr>) list>;
                    template : PosAdorn<Template> option }

// Value constructor. Type is optional.
and ValueCon =    PosAdorn<string> * (PosAdorn<TyExpr> option)

// Union algrebraic datatype. Template is optional.
and UnionRec =    { name     : PosAdorn<string>;
                    valCons  : PosAdorn<ValueCon list>;
                    template : PosAdorn<Template> option }

// Let statement for functional-style declarations.
and LetDecRec = { varName : PosAdorn<string>;
                  typ     : PosAdorn<TyExpr> option;
                  right   : PosAdorn<Expr>; }

// Declaration defined as any of the above.
and Declaration = FunctionDec   of FunctionRec
                | RecordDec     of RecordRec
                | UnionDec      of UnionRec
                | LetDec        of LetDecRec
                | ModuleNameDec of PosAdorn<string>
                | OpenDec       of PosAdorn<PosAdorn<string> list>
                | IncludeDec    of PosAdorn<PosAdorn<string> list>

// A template is associated with a function, record or union
and Template = { tyVars : PosAdorn<PosAdorn<string> list>; capVars : PosAdorn<PosAdorn<string> list> option }

// Use these to apply a template (ex: when calling a function with a template)
and TemplateApply = { tyExprs : PosAdorn<PosAdorn<TyExpr> list>; capExprs : PosAdorn<PosAdorn<CapacityExpr> list> }

// Capacities are used for making lists and arrays of fixed maximum sizes.
and CapacityArithOp = CapAdd | CapSubtract | CapMultiply | CapDivide
and CapacityUnaryOp = CapNegate
and CapacityArithOpRec = { left : PosAdorn<CapacityExpr>; op : PosAdorn<CapacityArithOp>; right : PosAdorn<CapacityExpr> }
and CapacityUnaryOpRec = { op : PosAdorn<CapacityUnaryOp>; term : PosAdorn<CapacityExpr> }
and CapacityExpr = CapacityNameExpr of PosAdorn<string>
                 | CapacityOp of CapacityArithOpRec
                 | CapacityUnaryOp of CapacityUnaryOpRec
                 | CapacityConst of PosAdorn<int64>

// The language is statically typed, and so there must be support for Type Expressons and their applications
// (applying a typed datatype, typed arrays, typed functions definitions, a list of base types).
and TyApplyRec = { tyConstructor : PosAdorn<TyExpr>; args : PosAdorn<TemplateApply> }
and ArrayTyRec = { valueType : PosAdorn<TyExpr>; capacity : PosAdorn<CapacityExpr> }
and FunTyRec = { template : PosAdorn<Template> option; args : PosAdorn<TyExpr> list; returnType : PosAdorn<TyExpr> }
and BaseTypes = TyUint8
              | TyUint16
              | TyUint32
              | TyUint64
              | TyInt8
              | TyInt16
              | TyInt32
              | TyInt64
              | TyFloat
              | TyDouble
              | TyBool
              | TyUnit
              | TyPointer
and TyExpr = BaseTy of PosAdorn<BaseTypes>
           | ModuleQualifierTy of ModQualifierRec
           | NameTy of PosAdorn<string>
           | ApplyTy of TyApplyRec
           | ArrayTy of ArrayTyRec
           | FunTy of FunTyRec
           | VarTy of PosAdorn<string>
           | RefTy of PosAdorn<TyExpr>
           | TupleTy of PosAdorn<TyExpr> list
           // Need this extra type for infix parser combinator matching on tuples
           | ParensTy of PosAdorn<TyExpr>

// Pattern matching AST datatypes.
and MatchVarRec = {varName : PosAdorn<string>; mutable_ : PosAdorn<bool>; typ : PosAdorn<TyExpr> option}
and MatchValConRec = { name : PosAdorn<Choice<string, ModQualifierRec>>; template : PosAdorn<TemplateApply> option; innerPattern : PosAdorn<Pattern> option }
and MatchRecConRec = { name : PosAdorn<Choice<string, ModQualifierRec>>; template : PosAdorn<TemplateApply> option; fields : PosAdorn<(PosAdorn<string> * PosAdorn<Pattern>) list>}

and Pattern = MatchVar of MatchVarRec
            | MatchIntVal of PosAdorn<int64>
            | MatchFloatVal of PosAdorn<float>
            | MatchValCon of MatchValConRec
            | MatchRecCon of MatchRecConRec
            | MatchUnderscore of PosAdorn<unit>
            | MatchTuple of PosAdorn<PosAdorn<Pattern> list>
            | MatchUnit of PosAdorn<unit>
            | MatchTrue of PosAdorn<unit>
            | MatchFalse of PosAdorn<unit>

// Elements of a function clause.
and FunctionClause = {returnTy : PosAdorn<TyExpr> option; arguments : PosAdorn<(PosAdorn<string> * (PosAdorn<TyExpr> option)) list>; body : PosAdorn<Expr>}

// Module qualifier.
and ModQualifierRec = { module_ : PosAdorn<string>; name : PosAdorn<string> }

and Direction = Upto
              | Downto

// Other AST objects and their definitions. Most of them are explained within their names.
// Binary operation
and BinaryOpRec =     { left : PosAdorn<Expr>; op : PosAdorn<BinaryOps>; right : PosAdorn<Expr> }
and IfElseRec =       { condition : PosAdorn<Expr>; trueBranch : PosAdorn<Expr>; falseBranch : PosAdorn<Expr> }
and LetRec =          { left : PosAdorn<Pattern>; right : PosAdorn<Expr> }
// Variable assign
and AssignRec =       { left : PosAdorn<LeftAssign>; right : PosAdorn<Expr>; ref : PosAdorn<bool> }
and ForLoopRec =      { typ : PosAdorn<TyExpr> option; varName : PosAdorn<string>; start : PosAdorn<Expr>; direction : PosAdorn<Direction>; end_ : PosAdorn<Expr>; body : PosAdorn<Expr> }
and WhileLoopRec =    { condition : PosAdorn<Expr>; body : PosAdorn<Expr> }
and DoWhileLoopRec =  { condition : PosAdorn<Expr>; body: PosAdorn<Expr> }
// Pattern matching
and CaseRec =         { on : PosAdorn<Expr>; clauses : PosAdorn<(PosAdorn<Pattern> * PosAdorn<Expr>) list> }
// Unary operation
and UnaryOpRec =      { op : PosAdorn<UnaryOps>; exp : PosAdorn<Expr> }
and RecordAccessRec = { record : PosAdorn<Expr>; fieldName : PosAdorn<string> }
and ArrayAccessRec =  { array : PosAdorn<Expr>; index : PosAdorn<Expr> }
and InternalDeclareVarExpRec = { varName : PosAdorn<string>; typ : PosAdorn<TyExpr> option; right : PosAdorn<Expr> }
and InternalValConAccessRec = { valCon : PosAdorn<Expr>; typ : PosAdorn<TyExpr> }
and InternalTupleAccessRec = { tuple : PosAdorn<Expr>; index : int }
// Function call/apply
and CallRec =         { func : PosAdorn<Expr>; args : PosAdorn<PosAdorn<Expr> list> }
// Applying the template of a function
and TemplateApplyExpRec = { func : PosAdorn<Choice<string, ModQualifierRec>>; templateArgs : PosAdorn<TemplateApply> }
and RecordExprRec =   { recordTy : PosAdorn<Choice<string, ModQualifierRec>>; templateArgs : PosAdorn<TemplateApply> option; initFields : PosAdorn<(PosAdorn<string> * PosAdorn<Expr>) list> }
and ArrayMakeExpRec = { typ : PosAdorn<TyExpr>; initializer : PosAdorn<Expr> option }
and TypeConstraintRec = { exp : PosAdorn<Expr>; typ : PosAdorn<TyExpr> }
and Expr = SequenceExp of PosAdorn<PosAdorn<Expr> list>
          | BinaryOpExp of BinaryOpRec
          | IfElseExp of IfElseRec
          | LetExp of LetRec
          //| InternalDeclareVar of InternalDeclareVarExpRec // Only used internally for declaring variables
                                                           // that will actually be outputted by the compiler
          //| InternalValConAccess of InternalValConAccessRec // Only used internally for type checking pattern
                                                            // matching. Essentially acts like a type cast
          //| InternalTupleAccess of InternalTupleAccessRec
          | InlineCode of PosAdorn<string>
          | AssignExp of AssignRec
          | ForLoopExp of ForLoopRec
          | WhileLoopExp of WhileLoopRec
          | DoWhileLoopExp of DoWhileLoopRec
          | CaseExp of CaseRec
          | UnaryOpExp of UnaryOpRec
          | RecordAccessExp of RecordAccessRec
          | ArrayAccessExp of ArrayAccessRec
          | VarExp of PosAdorn<string>
          | UnitExp of PosAdorn<unit>
          | TrueExp of PosAdorn<unit>
          | FalseExp of PosAdorn<unit>
          | LambdaExp of PosAdorn<FunctionClause>
          | IntExp of PosAdorn<int64>
          | FloatExp of PosAdorn<float>
          | CallExp of CallRec
          | TemplateApplyExp of TemplateApplyExpRec
          | ModQualifierExp of PosAdorn<ModQualifierRec>
          | RecordExp of RecordExprRec
          | ArrayLitExp of PosAdorn<PosAdorn<Expr> list>
          | ArrayMakeExp of ArrayMakeExpRec
          | RefExp of PosAdorn<Expr>
          | DerefExp of PosAdorn<Expr>
          | TupleExp of PosAdorn<Expr> list
          | NullExp of PosAdorn<unit>
          | QuitExp of PosAdorn<TyExpr> option
          | TypeConstraint of TypeConstraintRec
and BinaryOps = Add | Subtract | Multiply | Divide | Modulo | BitwiseOr | BitwiseAnd | BitwiseXor
              | LogicalOr | LogicalAnd | Equal | NotEqual | GreaterOrEqual | LessOrEqual | Greater | Less
              | BitshiftLeft | BitshiftRight
and UnaryOps = LogicalNot | BitwiseNot | Negate

// Mutations are changes in already declared variables, arrays, records, etc.
and ArrayMutationRec =  { array : PosAdorn<LeftAssign>; index : PosAdorn<Expr> }
and RecordMutationRec = { record : PosAdorn<LeftAssign>; fieldName : PosAdorn<string> }
and LeftAssign = VarMutation of PosAdorn<string>
               | ModQualifierMutation of PosAdorn<ModQualifierRec>
               | ArrayMutation of ArrayMutationRec
               | RecordMutation of RecordMutationRec

// Takes in a wrapped AST object, returns the object within the PosAdorn.
let unwrap<'a> ((_, c) : PosAdorn<'a>) = c
// Takes in a wrapped AST object, returns the starting position.
let getPos<'a> ((a, _) : PosAdorn<'a>) = a
// Takes in a wrapped AST object, returns the ending position.
//let getType<'a> ((_, b, _) : PosAdorn<'a>) = b
// Dummy position used for initializing positions on PosAdorns
(*let dummyPos : Position = {pos_fname=""
                           pos_lnum = -1
                           pos_bol = -1
                           pos_cnum = -1}
let dummyWrap<'a> c : PosAdorn<'a> = ((dummyPos, dummyPos), None, c)
// Cleans up the wrapping around an AST object, returns it to default dummy values.
let clean<'a> ((_, _, c) : PosAdorn<'a>) : PosAdorn<'a> = dummyWrap c
let cleanAll haystack = TreeTraversals.map1 (fun pos -> dummyPos) haystack

// Add typing to a PosAdorn.
let wrapWithType<'a> t c : PosAdorn<'a> = ((dummyPos, dummyPos), Some t, c)

let templateToTemplateApply template =
    let tyExprs = template.tyVars |> unwrap |> List.map (ForallTy >> dummyWrap) |> dummyWrap
    let capExprs = template.capVars |> unwrap |> List.map (CapacityNameExpr >> dummyWrap) |> dummyWrap
    {tyExprs=tyExprs; capExprs=capExprs}*)

(*
let rec mapCapacityExpr (h : CapacityExpr -> CapacityExpr) ((posc, cap) : PosAdorn<CapacityExpr>) : PosAdorn<CapacityExpr> =
    let c = mapCapacityExpr h
    let cap' =
        match cap with
        | (CapacityNameExpr _ | CapacityConst _) ->
            cap
        | CapacityOp {left=left; op=op; right=right} ->
            CapacityOp {left=c left; op=op; right=c right}
        | CapacityUnaryOp {op=op; term=term} ->
            CapacityUnaryOp {op=op; term=c term}
    (posc, h cap')

and mapTemplateApply (g : TyExpr -> TyExpr) (h : CapacityExpr -> CapacityExpr) ((post, typ) : PosAdorn<TemplateApply>) : PosAdorn<TemplateApply> =
    failwith "not implemented"

and mapType f g h k (post, typ) =
    let t = mapType f g h k
    let typ' =
        match typ with
        | ApplyTy {tyConstructor=tyConstructor; args=args} ->
            ApplyTy {tyConstructor=t tyConstructor; args=mapTemplateApply g h args}
        | ArrayTy {valueType=valueType; capacity=capacity} ->
            ArrayTy {valueType=t valueType; capacity=mapCapacityExpr h capacity}
        | (BaseTy _ | ModuleQualifierTy _ | NameTy _ | VarTy _) ->
            typ
        | FunTy {template=template; args=args; returnType=returnType} ->
            FunTy {template=template; args=List.map t args; returnType=returnType}
        | ParensTy ty ->
            ParensTy (t ty)
        | RefTy ty ->
            RefTy (t ty)
        | TupleTy tys ->
            TupleTy (List.map t tys)
    (post, g typ')

and mapLeftAssign f g h k (pose, left) =
    let l = mapLeftAssign f g h k
    let left' =
        match left with
        | ArrayMutation {array=array; index=index} ->
            ArrayMutation {array=l array; index=mapExpr f g h k index}
        | (ModQualifierMutation _ | VarMutation _) ->
            left
        | RecordMutation {record=record; fieldName=fieldName} ->
            RecordMutation {record=l record; fieldName=fieldName}
    (pose, left')
            

and mapPattern f g h k (post, pat) =
    let p = mapPattern f g h k
    let pat' =
        match pat with
        | (MatchFloatVal _ | MatchTrue _ | MatchFalse _ | MatchUnit _ | MatchIntVal _ | MatchUnderscore _ | MatchVar _) ->
            pat
        | MatchRecCon {typ=typ; fields=(posf, fields)} ->
            MatchRecCon {typ=mapType f g h k typ; fields=(posf, List.map (fun (name, fieldPattern) -> (name, p fieldPattern)) fields)}
        | MatchTuple (postup, patterns) ->
            MatchTuple (postup, List.map p patterns) 
        | MatchValCon {name=name; template=template; innerPattern=innerPattern} ->
            MatchValCon {name=name; template=Option.map (mapTemplateApply g h) template; innerPattern=Option.map p innerPattern}
    (post, k pat')

and mapExpr f g h k (pose, e) =
    let m = mapExpr f g h k
    let t = mapType f g h k
    let e' =
        match e with
        | ArrayAccessExp {array = array; index=index} ->
            ArrayAccessExp {array=m array; index=m index}
        | ArrayLitExp (p, exps) ->
            ArrayLitExp (p, List.map m exps)
        | ArrayMakeExp {typ=typ; initializer=initializer} ->
            ArrayMakeExp {typ=t typ; initializer=Option.map m initializer}
        | AssignExp {left=left; right=right; ref=ref} ->
            AssignExp {left=mapLeftAssign f g h k left; right=m right; ref=ref}
        | BinaryOpExp {left=left; op=op; right=right} ->
            BinaryOpExp {left=m left; op=op; right=m right}
        | CallExp {func=func; args=(posa, args)} ->
            CallExp {func=m func; args=(posa, List.map m args)}
        | CaseExp {on=on; clauses=(posc, clauses)} ->
            CaseExp {on=m on; clauses=(posc, List.map (fun (pattern, clauseExp) -> (mapPattern f g h k pattern, m clauseExp)) clauses)}
        | DerefExp expr ->
            DerefExp (m expr)
        | DoWhileLoopExp {condition=condition; body=body} ->
            DoWhileLoopExp {condition=m condition; body=m body}
        | (FalseExp _ | FloatExp _ | TrueExp _ | IntExp _ | InlineCode _ | ModQualifierExp _ | NullExp _ | UnitExp _ | VarExp _) ->
            e
        | ForLoopExp {typ=typ; varName=varName; start=start; direction=direction; end_=end_; body=body} ->
            ForLoopExp {typ=Option.map t typ; varName=varName; start=m start; direction=direction; end_=m end_; body=m body}
        | IfElseExp {condition=condition; trueBranch=trueBranch; falseBranch=falseBranch} ->
            IfElseExp {condition=m condition; trueBranch=m trueBranch; falseBranch=m falseBranch}
        | LambdaExp (p, {returnTy=returnTy; arguments=(posa, arguments); body=body}) ->
            LambdaExp (p, {arguments=(posa, List.map (fun (name, maybeType) -> (name, Option.map t maybeType)) arguments);
                           returnTy=Option.map t returnTy;
                           body=m body})
        | LetExp {left=left; right=right} ->
            LetExp {left=mapPattern f g h k left; right=m right}
        | QuitExp ty ->
            QuitExp (t ty)
        | RecordAccessExp {record=record; fieldName=fieldName} ->
            RecordAccessExp {record=m record; fieldName=fieldName}
        | RecordExp {recordTy=recordTy; templateArgs=templateArgs; initFields=(posi, initFields)} ->
            RecordExp {recordTy=t recordTy;
                       templateArgs=Option.map (mapTemplateApply g h) templateArgs;
                       initFields=(posi, List.map (fun (name, fieldExpr) -> (name, m fieldExpr)) initFields)}
        | RefExp expr ->
            RefExp (m expr)
        | SequenceExp (p, exps) ->
            SequenceExp (p, List.map m exps)
        | TemplateApplyExp {func=func; templateArgs=templateArgs} ->
            TemplateApplyExp {func=m func; templateArgs=mapTemplateApply g h templateArgs}
        | TupleExp exprs ->
            TupleExp (List.map m exprs)
        | TypeConstraint {exp=exp; typ=typ} ->
            TypeConstraint {exp=m exp; typ=t typ}
        | UnaryOpExp {op=op; exp=exp} ->
            UnaryOpExp {op=op; exp=m exp}
        | WhileLoopExp {condition=condition; body=body} ->
            WhileLoopExp {condition=m condition; body=m body}
    (pose, f e')

let mapDec f g h k (posd, dec) =
    match dec with
    | FunctionDec {name=name; template=template; clause=(posc, {returnTy=returnTy; arguments=(posa, arguments); body=body})} ->
        let (names, taus) = List.unzip arguments
        let taus' = List.map (Option.map (mapType f g h k)) taus
        FunctionDec {
            name=name;
            template=template;
            clause=(posc, {
                returnTy=Option.map (mapType f g h k) returnTy;
                arguments=(posa, List.zip names taus')
                body=mapExpr f g h k body
            })
        }
    | RecordDec {name=name; template=template; fields=(posf, fields)} ->
        let (fieldNames, taus) = List.unzip fields
        let taus' = List.map (mapType f g h k) taus
        RecordDec {name=name; template=template; fields=(posf, List.zip fieldNames taus')}
    | UnionDec {name=name; template=template; valCons=(posv, valCons)} ->
        let (names, taus) = List.unzip valCons
        let taus' = List.map (Option.map (mapType f g h k)) taus
        UnionDec {name=name; template=template; valCons=(posv, List.zip names taus')}
    | LetDec {varName=varName; typ=typ; right=right} ->
        LetDec {varName=varName; typ=Option.map (mapType f g h k) typ; right=mapExpr f g h k right}
    | _ -> dec
        

let foldExpr f g h k accum0 expr =
    let state = ref accum0
    mapExpr
        (fun x ->
            state := f !state x
            x)
        (fun x ->
            state := g !state x
            x)
        (fun x ->
            state := h !state x
            x)
        (fun x ->
            state := k !state x
            x)
        expr |> ignore
    !state

let mapFoldExpr f g h k accum0 expr =
    let state = ref accum0
    let res =
        mapExpr
            (fun x ->
                let (accum1, x') = f !state x
                state := accum1
                x')
            (fun x ->
                let (accum1, x') = g !state x
                state := accum1
                x')
            (fun x ->
                let (accum1, x') = h !state x
                state := accum1
                x')
            (fun x ->
                let (accum1, x') = k !state x
                state := accum1
                x')
            expr
    (!state, res)

let mapFoldId =
    fun accum0 value ->
        (accum0, value)

*)