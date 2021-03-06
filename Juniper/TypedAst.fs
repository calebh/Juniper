﻿module TypedAst
open FParsec
open Extensions

// Allows for module type to be used for declaring modules.
type Module = Module of Declaration list

// Tuple of starting position and ending position
// Note: The 'option' keyword indicates that field is optional (can have 'none' as assignment)

// PosAdorn wraps a an AST object in a start and end line position for helpful debugging
// messages. It also includes the type of the object, which starts as 'none'.
// Virtually every object in the AST is a PosAdorn wrapping another object.
and TyAdorn<'a> = (Position * Position) * TyExpr * 'a

// Top level declarations
and FunctionRec = { name     : string;
                    template : Template option;
                    clause   : FunctionClause }

and AliasRec  =   { name     : string
                    template : Template option;
                    typ : TyExpr }

and ValueCon =    string * (TyExpr list)

// Union algrebraic datatype
and UnionRec =    { name     : string;
                    valCons  : ValueCon list;
                    template : Template option }

// Let statement
and LetDecRec = { varName : string;
                  typ     : TyExpr;
                  right   : TyAdorn<Expr> }

// Declaration defined as any of the above.
and Declaration = FunctionDec   of FunctionRec
                | AliasDec      of AliasRec
                | UnionDec      of UnionRec
                | LetDec        of LetDecRec
                | ModuleNameDec of string
                | OpenDec       of string list
                | IncludeDec    of string list
                | InlineCodeDec of string

// A template is associated with a function, record or union
and Template = { tyVars : string list; capVars : string list }

// Use these to apply a template (ex: when calling a function with a template)
and TemplateApply = { tyExprs : TyExpr list; capExprs : CapacityExpr list }

// Capacities are used for making lists and arrays of fixed maximum sizes.
and CapacityArithOp = CapAdd | CapSubtract | CapMultiply | CapDivide
and CapacityUnaryOp = CapNegate
and CapacityArithOpRec = { left : CapacityExpr; op : CapacityArithOp; right : CapacityExpr }
and CapacityUnaryOpRec = { op : CapacityUnaryOp; term : CapacityExpr }
and CapacityExpr = CapacityVar of string
                 | CapacityOp of CapacityArithOpRec
                 | CapacityUnaryOp of CapacityUnaryOpRec
                 | CapacityConst of int64

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
              | TyString
              | TyRawPointer
and TyCons = BaseTy of BaseTypes
           | ModuleQualifierTy of ModQualifierRec
           | ArrayTy
           | FunTy
           | RefTy
           | TupleTy
and TyExpr = TyCon of TyCons
                    // For TyCon FunTy, the first element is the closure, the second element in the TyExpr list is the return type
                    // v this must be a TyCon
           | ConApp of TyExpr * (TyExpr list) * (CapacityExpr list)
           | TyVar of string
                          // The (string list) option indicates the ordering for packed records
           | RecordTy of ((string list) option * Map<string, TyExpr>)
           | ClosureTy of Map<string, TyExpr>
and ConstraintType = IsNum | IsInt | IsReal | IsPacked | HasField of (string * TyExpr) | IsRecord
                      // v Types       v capacities  v constraints on types
and TyScheme = Forall of string list * string list * ((TyExpr * ConstraintType) list) * TyExpr

and DeclarationTy = FunDecTy of TyScheme
                    //              v Types      v capacities
                  | AliasDecTy of string list * string list * TyExpr
                  | LetDecTy of TyExpr
                  | UnionDecTy of string list * string list * ModQualifierRec

// Pattern matching AST datatypes.
and MatchVarRec = { varName : string; mutable_ : bool; typ : TyExpr }
and MatchValConRec = { modQualifier : ModQualifierRec; innerPattern : TyAdorn<Pattern> list; id : int }

and Pattern = MatchVar of MatchVarRec
            | MatchIntVal of int64
            | MatchFloatVal of float
            | MatchValCon of MatchValConRec
            | MatchRecCon of (string * TyAdorn<Pattern>) list
            | MatchUnderscore
            | MatchTuple of TyAdorn<Pattern> list
            | MatchUnit
            | MatchTrue
            | MatchFalse

// Elements of a function clause.
and FunctionClause = {closure : Map<string, TyExpr>; returnTy : TyExpr; arguments : (string * TyExpr) list; body : TyAdorn<Expr>}

// Module qualifier.
and ModQualifierRec = { module_ : string; name : string }

and Direction = Upto
              | Downto

// Other AST objects and their definitions. Most of them are explained within their names.
// Binary operation
and BinaryOpRec =     { left : TyAdorn<Expr>; op : BinaryOps; right : TyAdorn<Expr> }
and IfElseRec =       { condition : TyAdorn<Expr>; trueBranch : TyAdorn<Expr>; falseBranch : TyAdorn<Expr> }
and LetRec =          { left : TyAdorn<Pattern>; right : TyAdorn<Expr> }
// Variable assign
and AssignRec =       { left : TyAdorn<LeftAssign>; right : TyAdorn<Expr>; ref : bool }
and ForLoopRec =      { typ : TyExpr; varName : string; start : TyAdorn<Expr>; direction : Direction; end_ : TyAdorn<Expr>; body : TyAdorn<Expr> }
and WhileLoopRec =    { condition : TyAdorn<Expr>; body : TyAdorn<Expr> }
and DoWhileLoopRec =  { condition : TyAdorn<Expr>; body: TyAdorn<Expr> }
// Pattern matching
and CaseRec =         { on : TyAdorn<Expr>; clauses : (TyAdorn<Pattern> * TyAdorn<Expr>) list }
// Unary operation
and UnaryOpRec =      { op : UnaryOps; exp : TyAdorn<Expr> }
and RecordAccessRec = { record : TyAdorn<Expr>; fieldName : string }
and ArrayAccessRec =  { array : TyAdorn<Expr>; index : TyAdorn<Expr> }
and InternalDeclareVarExpRec = { varName : string; typ : TyExpr; right : TyAdorn<Expr> }
and InternalUsingRec = { varName : string; typ : TyExpr }
and InternalUsingCapRec = { varName : string; cap : CapacityExpr }
and UnsafeTypeCastRec = { exp : TyAdorn<Expr>; typ : TyExpr }
// Function call/apply
and CallRec =         { func : TyAdorn<Expr>; args : TyAdorn<Expr> list }
// Applying the template of a function
and TemplateApplyExpRec = { func : Choice<string, ModQualifierRec>; templateArgs : TemplateApply }
and RecordExprRec =   { packed : bool; initFields : (string * TyAdorn<Expr>) list }
and ArrayMakeExpRec = { typ : TyExpr; initializer : TyAdorn<Expr> option }
and DeclVarExpRec = { varName : string; typ : TyExpr }
and Expr = SequenceExp of TyAdorn<Expr> list
          | BinaryOpExp of BinaryOpRec
          | IfElseExp of IfElseRec
          | LetExp of LetRec
          | DeclVarExp of DeclVarExpRec
          | InternalDeclareVar of InternalDeclareVarExpRec // Only used internally for declaring variables
                                                           // that will actually be outputted by the compiler
          | InternalUsing of InternalUsingRec
          | InternalUsingCap of InternalUsingCapRec
          | InlineCode of string
          | AssignExp of AssignRec
          | ForLoopExp of ForLoopRec
          | WhileLoopExp of WhileLoopRec
          | DoWhileLoopExp of DoWhileLoopRec
          | CaseExp of CaseRec
          | UnaryOpExp of UnaryOpRec
          | RecordAccessExp of RecordAccessRec
          | ArrayAccessExp of ArrayAccessRec
          | VarExp of string * TyExpr list * CapacityExpr list
          | UnitExp
          | TrueExp
          | FalseExp
          | LambdaExp of FunctionClause
          | IntExp of int64
          | Int8Exp of int64
          | UInt8Exp of int64
          | Int16Exp of int64
          | UInt16Exp of int64
          | Int32Exp of int64
          | UInt32Exp of int64
          | Int64Exp of int64
          | UInt64Exp of int64
          | FloatExp of float
          | DoubleExp of float
          | StringExp of string
          | CallExp of CallRec
          | TemplateApplyExp of TemplateApplyExpRec
          | ModQualifierExp of ModQualifierRec * TyExpr list * CapacityExpr list
          | RecordExp of RecordExprRec
          | ArrayLitExp of TyAdorn<Expr> list
          | ArrayMakeExp of ArrayMakeExpRec
          | RefExp of TyAdorn<Expr>
          | TupleExp of TyAdorn<Expr> list
          | QuitExp of TyExpr
          | Smartpointer of TyAdorn<Expr> * TyAdorn<Expr>
          | NullExp
          | FunctionWrapperEmptyClosure of TyAdorn<Expr>
and BinaryOps = Add | Subtract | Multiply | Divide | Modulo | BitwiseOr | BitwiseAnd | BitwiseXor
              | LogicalOr | LogicalAnd | Equal | NotEqual | GreaterOrEqual | LessOrEqual | Greater | Less
              | BitshiftLeft | BitshiftRight
and UnaryOps = LogicalNot | BitwiseNot | Negate | Deref

// Mutations are changes in already declared variables, arrays, records, etc.
and ArrayMutationRec =  { array : LeftAssign; index : TyAdorn<Expr> }
and RecordMutationRec = { record : LeftAssign; fieldName : string }
and LeftAssign = VarMutation of string
               | ModQualifierMutation of ModQualifierRec
               | ArrayMutation of ArrayMutationRec
               | RecordMutation of RecordMutationRec

// Takes in a wrapped AST object, returns the object within the TyAdorn.
let unwrap<'a> ((_, _, c) : TyAdorn<'a>) = c
let getType<'a> ((_, b, _) : TyAdorn<'a>) = b
let getPos<'a> ((a, _, _) : TyAdorn<'a>) = a

let dummyPos : Position = new Position("", -1L, -1L, -1L)

let dummyWrap<'a> c : TyAdorn<'a> = ((dummyPos, dummyPos), TyCon <| BaseTy TyUnit, c)

// Add typing to a TyAdorn.
let wrapWithType<'a> t c : TyAdorn<'a> = ((dummyPos, dummyPos), t, c)

// Turns a capacity expression into a string for debugging (printing error messages)
let rec capacityString cap =
    match cap with
    | CapacityVar name -> name
    | CapacityOp {left=left; op=op; right=right} ->
        let opStr = match op with
                    | CapAdd -> "+"
                    | CapSubtract -> "-"
                    | CapDivide -> "/"
                    | CapMultiply -> "*"
        sprintf "(%s %s %s)" (capacityString left) opStr (capacityString right)
    | CapacityConst number -> sprintf "%i" number
    | CapacityUnaryOp {op=CapNegate; term=term} -> sprintf "-%s" (capacityString term)

let rec typeConString con appliedTo capExprs =
    let typeStrings tys sep = List.map typeString tys |> String.concat sep
    let capacityStrings caps sep = List.map capacityString caps |> String.concat sep
    match con with
    | BaseTy baseTy ->
        match baseTy with
        | TyUint8 -> "uint8"
        | TyUint16 -> "uint16"
        | TyUint32 -> "uint32"
        | TyUint64 -> "uint64"
        | TyInt8 -> "int8"
        | TyInt16 -> "int16"
        | TyInt32 -> "int32"
        | TyInt64 -> "int64"
        | TyBool -> "bool"
        | TyUnit -> "unit"
        | TyFloat -> "float"
        | TyDouble -> "double"
        | TyPointer -> "pointer"
        | TyString -> "string"
        | TyRawPointer -> "rawpointer"
    | ArrayTy ->
        let [arrTy] = appliedTo
        let size =
            match capExprs with
            | [size] ->
                capacityString size
            | _ ->
                "???"
        sprintf "%s[%s]" (typeString arrTy) size
    | FunTy ->
        let closureTy::retTy::argsTys = appliedTo
        sprintf "(%s)(%s) -> %s" (typeString closureTy) (typeStrings argsTys ", ") (typeString retTy)
    | ModuleQualifierTy {module_=module_; name=name} ->
        let genericApplication =
            match appliedTo with
            | [] -> ""
            | _ ->
                if List.length capExprs = 0 then
                    sprintf "<%s>" (typeStrings appliedTo ", ")
                else
                    sprintf "<%s; %s>" (typeStrings appliedTo ", ") (capacityStrings capExprs ", ")
        sprintf "%s:%s%s" module_ name genericApplication
    | RefTy ->
        match appliedTo with
        | [refTy] -> sprintf "%s ref" (typeString refTy)
        | _ -> "ref"
    | TupleTy ->
        typeStrings appliedTo " * "

and typeString (ty : TyExpr) : string =
    match ty with
    | TyCon con ->
        typeConString con [] []
    | ConApp (TyCon con, args, capArgs) ->
        typeConString con args capArgs
    | TyVar name ->
        sprintf "'%s" name
    | RecordTy (Some packed, fields) ->
        sprintf "packed {%s}" (packed |> List.map (fun fieldName -> sprintf "%s : %s" fieldName (Map.find fieldName fields |> typeString)) |> String.concat "; ")
    | RecordTy (None, fields) ->
        sprintf "{%s}" (fields |> Map.toList |> List.map (fun (fieldName, fieldTau) -> sprintf "%s : %s" fieldName (typeString fieldTau)) |> String.concat "; ")
    | ClosureTy fields ->
        sprintf "|%s|" (fields |> Map.toList |> List.map (fun (fieldName, fieldTau) -> sprintf "%s : %s" fieldName (typeString fieldTau)) |> String.concat "; ")
    | ConApp (con, args, capArgs) ->
        match capArgs with
        | [] ->
            sprintf "%s<%s>" (typeString con) (args |> List.map typeString |> String.concat ", ")
        | _ ->
            sprintf "%s<%s; %s>" (typeString con) (args |> List.map typeString |> String.concat ", ") (capArgs |> List.map capacityString |> String.concat ", ")

and interfaceConstraintString (interfaceConstraint : ConstraintType) =
    match interfaceConstraint with
    | IsNum -> "num"
    | IsInt -> "int"
    | IsReal -> "real"
    | IsPacked -> "packed"
    | HasField (fieldName, fieldTau) -> sprintf "{%s : %s}" fieldName (typeString fieldTau)
    | IsRecord -> "record"

let schemeString (scheme : TyScheme) : string =
    let s1 =
        match scheme with
        | Forall ([], [], _, _) ->
            ""
        | Forall (typeVars, [], _, _) ->
            typeVars |> List.map (fun t -> "'" + t) |> String.concat ", "
        | Forall (typeVars, capVars, _, _) ->
            (typeVars |> List.map (fun t -> "'" + t) |> String.concat ", ") + "; " + (capVars |> String.concat ", ")
    let (Forall (_, _, interfaceConstraints, tau)) = scheme
    let s2 = sprintf "<%s>%s" s1 (typeString tau)
    let s3 =
        match interfaceConstraints with
        | [] -> ""
        | _ -> sprintf " where %s" (interfaceConstraints |> List.map (fun (tau, constr) -> sprintf "%s : %s" (typeString tau) (interfaceConstraintString constr)) |> String.concat ", ")
    s2 + s3

let baseTy b = TyCon <| BaseTy b
let unittype = baseTy TyUnit
let booltype = baseTy TyBool
let int8type = baseTy TyInt8
let uint8type = baseTy TyUint8
let int16type = baseTy TyInt16
let uint16type = baseTy TyUint16
let int32type = baseTy TyInt32
let uint32type = baseTy TyUint32
let int64type = baseTy TyInt64
let uint64type = baseTy TyUint64
let floattype = baseTy TyFloat
let doubletype = baseTy TyDouble
let pointertype = baseTy TyPointer
let stringtype = baseTy TyString
let rawpointertype = baseTy TyRawPointer

let closureFromFunTy (ConApp (TyCon FunTy, ClosureTy closure::_, _)) = closure
let returnFromFunTy (ConApp (TyCon FunTy, _::retTy::_, _)) = retTy
let argsFromFunTy (ConApp (TyCon FunTy, _::_::argsTy, _)) = argsTy

let wrapLike (from : TyAdorn<'a>) (to' : 'a) : TyAdorn<'a> =
    (getPos from, getType from, to')

let templateToTemplateApply ({tyVars=tyVars; capVars=capVars} : Template) : TemplateApply =
    {tyExprs=tyVars |> List.map TyVar; capExprs=capVars |> List.map CapacityVar}

// Generic functions for walking and mapping a typed AST
let rec patternToGamma (pat : TyAdorn<Pattern>) : Map<string, TyExpr> =
    match unwrap pat with
    | MatchValCon {innerPattern=innerPattern} ->
        innerPattern |> List.map patternToGamma |> Map.mergeMany
    | MatchRecCon fields ->
        fields |> List.map (snd >> patternToGamma) |> Map.mergeMany
    | MatchTuple inner ->
        inner |> List.map patternToGamma |> Map.mergeMany
    | (MatchFalse | MatchFloatVal _ | MatchIntVal _ | MatchTrue | MatchUnderscore | MatchUnit) ->
        Map.empty
    | MatchVar { varName=varName; typ=typ } ->
        Map.singleton varName typ

let rec preorderMapFoldLeftAssign (exprMapper: Map<string, TyExpr> -> 'accum -> TyAdorn<Expr> -> (TyAdorn<Expr> * 'accum))
                                  (leftAssignMapper: Map<string, TyExpr> -> 'accum -> LeftAssign -> (LeftAssign * 'accum))
                                  (patternMapper : Map<string, TyExpr> -> 'accum -> TyAdorn<Pattern> -> (TyAdorn<Pattern> * 'accum))
                                  (gamma : Map<string, TyExpr>) (accum : 'accum) (left : LeftAssign) : (LeftAssign * 'accum) =
    let preorderMapFoldLeftAssign' = preorderMapFoldLeftAssign exprMapper leftAssignMapper patternMapper gamma
    let (left', accum') = leftAssignMapper gamma accum left
    match left' with
    | VarMutation _ ->
        (left', accum')
    | ModQualifierMutation _ ->
        (left', accum')
    | ArrayMutation {array=array; index=index} ->
        let (array', accum'') = preorderMapFoldLeftAssign' accum' array
        let (index', accum''') = preorderMapFold exprMapper leftAssignMapper patternMapper gamma accum'' index
        (ArrayMutation {array=array'; index=index'}, accum''')
    | RecordMutation {record=record; fieldName=fieldName} ->
        let (record', accum'') = preorderMapFoldLeftAssign' accum' record
        (RecordMutation {record=record'; fieldName=fieldName}, accum'')

and preorderMapFoldPattern (patternMapper : Map<string, TyExpr> -> 'accum -> TyAdorn<Pattern> -> (TyAdorn<Pattern> * 'accum))
                           (gamma : Map<string, TyExpr>) (accum : 'accum) (pat : TyAdorn<Pattern>) : (TyAdorn<Pattern> * 'accum) =
    let preorderMapFoldPattern' = preorderMapFoldPattern patternMapper gamma
    let (pat', accum') = patternMapper gamma accum pat
    match unwrap pat' with
    | MatchValCon {modQualifier=modQualifier; innerPattern=innerPattern; id=id} ->
        let (innerPattern', accum'') = List.mapFold preorderMapFoldPattern' accum' innerPattern
        (wrapLike pat' (MatchValCon {modQualifier=modQualifier; innerPattern=innerPattern'; id=id}), accum'')
    | MatchRecCon fields ->
        let names = fields |> List.map fst
        let (fields', accum'') = fields |> List.map snd |> List.mapFold preorderMapFoldPattern' accum'
        (wrapLike pat' (MatchRecCon (List.zip names fields')), accum'')
    | MatchTuple inner ->
        let (inner', accum'') = inner |> List.mapFold preorderMapFoldPattern' accum'
        (wrapLike pat' (MatchTuple inner'), accum'')
    | (MatchFalse | MatchFloatVal _ | MatchIntVal _ | MatchTrue | MatchUnderscore | MatchUnit | MatchVar _) ->
        (pat', accum')

and preorderMapFold (exprMapper: Map<string, TyExpr> -> 'accum -> TyAdorn<Expr> -> (TyAdorn<Expr> * 'accum))
                    (leftAssignMapper: Map<string, TyExpr> -> 'accum -> LeftAssign -> (LeftAssign * 'accum))
                    (patternMapper : Map<string, TyExpr> -> 'accum -> TyAdorn<Pattern> -> (TyAdorn<Pattern> * 'accum))
                    (gamma : Map<string, TyExpr>) (accum : 'accum) (expr : TyAdorn<Expr>) : (TyAdorn<Expr> * 'accum) =
    let preorderMapFold' = preorderMapFold exprMapper leftAssignMapper patternMapper gamma
    let preorderMapFoldLeftAssign' = preorderMapFoldLeftAssign exprMapper leftAssignMapper patternMapper gamma
    let preorderMapFoldPattern' = preorderMapFoldPattern patternMapper gamma
    let (expr', accum') = exprMapper gamma accum expr
    match unwrap expr' with
    | ArrayAccessExp {array=array; index=index} ->
        let (array', accum'') = preorderMapFold' accum' array
        let (index', accum''') = preorderMapFold' accum'' index
        (wrapLike expr' (ArrayAccessExp {array=array'; index=index'}), accum''')
    | ArrayLitExp literals ->
        let (literals', accum'') = List.mapFold preorderMapFold' accum' literals
        (wrapLike expr' (ArrayLitExp literals'), accum'')
    | ArrayMakeExp {typ=typ; initializer=initializer} ->
        let (initializer', accum'') = Option.mapFold preorderMapFold' accum' initializer
        (wrapLike expr' (ArrayMakeExp {typ=typ; initializer=initializer'}), accum'')
    | AssignExp {left=left; right=right; ref=ref} ->
        let (left', accum'') = preorderMapFoldLeftAssign' accum' (unwrap left)
        let (right', accum''') = preorderMapFold' accum'' right
        (wrapLike expr' (AssignExp {left=wrapLike left left'; right=right'; ref=ref}), accum''')
    | BinaryOpExp {left=left; op=op; right=right} ->
        let (left', accum'') = preorderMapFold' accum' left
        let (right', accum''') = preorderMapFold' accum'' right
        (wrapLike expr' (BinaryOpExp {left=left'; op=op; right=right'}), accum''')
    | CallExp {func=func; args=args} ->
        let (func', accum'') = preorderMapFold' accum' func
        let (args', accum''') = List.mapFold preorderMapFold' accum'' args
        (wrapLike expr' (CallExp {func=func'; args=args'}), accum''')
    | CaseExp {on=on; clauses=clauses} ->
        let (on', accum'') = preorderMapFold' accum' on
        let (clauses', accum'''''') =
            clauses |>
            List.mapFold
                (fun accum''' (pat, expr) ->
                    let (pat', accum'''') = preorderMapFoldPattern' accum''' pat
                    let gamma' = patternToGamma pat'
                    let (expr', accum''''') = preorderMapFold exprMapper leftAssignMapper patternMapper gamma' accum'''' expr
                    ((pat', expr'), accum'''''))
                accum''
        (wrapLike expr' (CaseExp {on=on'; clauses=clauses'}), accum'''''')
    | DeclVarExp _ ->
        (expr', accum')
    | DoWhileLoopExp {condition=condition; body=body} ->
        let (condition', accum'') = preorderMapFold' accum' condition
        let (body', accum''') = preorderMapFold' accum'' condition'
        (wrapLike expr' (DoWhileLoopExp {condition=condition'; body=body'}), accum''')
    | DoubleExp _ ->
        (expr', accum')
    | FalseExp _ ->
        (expr', accum')
    | FloatExp _ ->
        (expr', accum')
    | ForLoopExp {typ=typ; varName=varName; start=start; direction=direction; end_=end_; body=body } ->
        let gamma' = Map.add varName typ gamma
        let (start', accum'') = preorderMapFold exprMapper leftAssignMapper patternMapper gamma' accum' start
        let (end_', accum''') = preorderMapFold exprMapper leftAssignMapper patternMapper gamma' accum'' end_
        let (body', accum'''') = preorderMapFold exprMapper leftAssignMapper patternMapper gamma' accum''' body
        (wrapLike expr' (ForLoopExp {typ=typ; varName=varName; start=start'; direction=direction; end_=end_'; body=body'}), accum'''')
    | FunctionWrapperEmptyClosure inner ->
        let (inner', accum'') = preorderMapFold' accum' inner
        (wrapLike expr' (FunctionWrapperEmptyClosure inner'), accum'')
    | IfElseExp {condition=condition; trueBranch=trueBranch; falseBranch=falseBranch} ->
        let (condition', accum'') = preorderMapFold' accum' condition
        let (trueBranch', accum''') = preorderMapFold' accum'' trueBranch
        let (falseBranch', accum'''') = preorderMapFold' accum''' falseBranch
        (wrapLike expr' (IfElseExp {condition=condition'; trueBranch=trueBranch'; falseBranch=falseBranch'}), accum'''')
    | InlineCode _ ->
        (expr', accum')
    | (IntExp _ | Int8Exp _ | UInt8Exp _ | Int16Exp _ | UInt16Exp _ | Int32Exp _ | UInt32Exp _ | Int64Exp _ | UInt64Exp _ | StringExp _) ->
        (expr', accum')
    | InternalDeclareVar {varName=varName; typ=typ; right=right} ->
        let (right', accum'') = preorderMapFold' accum' right
        (wrapLike expr' (InternalDeclareVar {varName=varName; typ=typ; right=right'}), accum'')
    | InternalUsing _ ->
        (expr', accum')
    | InternalUsingCap _ ->
        (expr', accum')
    | LambdaExp {closure=closureTy; returnTy=returnTy; arguments=arguments; body=body} ->
        let gamma' = Map.merge gamma (Map.ofList arguments)
        let (body', accum'') = preorderMapFold exprMapper leftAssignMapper patternMapper gamma' accum' body
        (wrapLike expr' (LambdaExp {closure=closureTy; returnTy=returnTy; arguments=arguments; body=body'}), accum'')
    | LetExp {left=left; right=right} ->
        let (right', accum'') = preorderMapFold' accum' right
        let (left', accum''') = preorderMapFoldPattern' accum'' left
        (wrapLike expr' (LetExp {left=left'; right=right'}), accum''')
    | ModQualifierExp _ ->
        (expr', accum')
    | NullExp ->
        (expr', accum')
    | QuitExp _ ->
        (expr', accum')
    | RecordAccessExp {record=record; fieldName=fieldName} ->
        let (record', accum'') = preorderMapFold' accum' record
        (wrapLike expr' (RecordAccessExp {record=record'; fieldName=fieldName}), accum'')
    | RecordExp {packed=packed; initFields=initFields} ->
        let names = initFields |> List.map fst
        let (fieldExprs', accum'') = initFields |> List.map snd |> List.mapFold preorderMapFold' accum'
        let initFields' = List.zip names fieldExprs'
        (wrapLike expr' (RecordExp {packed=packed; initFields=initFields'}), accum'')
    | RefExp refExpr ->
        let (refExpr', accum'') = preorderMapFold' accum' refExpr
        (wrapLike expr' (RefExp refExpr'), accum'')
    | SequenceExp seqExprs ->
        let (seqExprs', (_, accum'''')) =
            seqExprs |>
            List.mapFold
                (fun (gamma', accum'') seqElem ->
                    let (seqElem', accum''') = preorderMapFold exprMapper leftAssignMapper patternMapper gamma' accum'' seqElem
                    let gamma'' =
                        match unwrap seqElem' with
                        | LetExp {left=left} ->
                            (Map.merge gamma' (patternToGamma left))
                        | DeclVarExp {varName=varName; typ=typ} ->
                            Map.add varName typ gamma'
                        | _ ->
                            gamma'
                    (seqElem', (gamma'', accum''')))
                (gamma, accum')
        (wrapLike expr' (SequenceExp seqExprs'), accum'''')
    | Smartpointer (ptr, destructor) ->
        let (ptr', accum'') = preorderMapFold' accum' ptr
        let (destructor', accum''') = preorderMapFold' accum'' destructor
        (wrapLike expr' (Smartpointer (ptr', destructor')), accum''')
    | TemplateApplyExp _ ->
        (expr', accum')
    | TrueExp ->
        (expr', accum')
    | TupleExp tupleElements ->
        let (tupleElements', accum'') = tupleElements |> List.mapFold preorderMapFold' accum'
        (wrapLike expr' (TupleExp tupleElements'), accum'')
    | UnaryOpExp {op=op; exp=unaryExp} ->
        let (unaryExp', accum'') = preorderMapFold' accum' unaryExp
        (wrapLike expr' (UnaryOpExp {op=op; exp=unaryExp'}), accum'')
    | UnitExp ->
        (expr', accum')
    | VarExp _ ->
        (expr', accum')
    | WhileLoopExp {condition=condition; body=body} ->
        let (condition', accum'') = preorderMapFold' accum' condition
        let (body', accum''') = preorderMapFold' accum'' body
        (wrapLike expr' (WhileLoopExp {condition=condition'; body=body'}), accum''')


let preorderFold (exprFolder: Map<string, TyExpr> -> 'accum -> TyAdorn<Expr> -> 'accum)
                 (leftAssignFolder: Map<string, TyExpr> -> 'accum -> LeftAssign -> 'accum)
                 (patternFolder : Map<string, TyExpr> -> 'accum -> TyAdorn<Pattern> -> 'accum)
                 gamma accum (expr : TyAdorn<Expr>) : 'accum =
    preorderMapFold
        (fun gamma' accum' expr -> (expr, exprFolder gamma' accum' expr))
        (fun gamma' accum' leftAssign -> (leftAssign, leftAssignFolder gamma' accum' leftAssign))
        (fun gamma' accum' pattern -> (pattern, patternFolder gamma' accum' pattern))
        gamma
        accum
        expr |>
    snd