module TypedAst
open FParsec
open Error

// Module qualifier.
type ModQualifierRec = { module_ : string; name : string }

type Kind = Star | KFun of List<Kind> * Kind

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
               | TyConUserDefined of ModQualifierRec
               | TyConArray
               | TyConFun // the first element in a TyConFun TApExpr is the return type, rest are arguments
               | TyConRef
               | TyConTuple

type TyCon = TyCon of BaseTyCon * Kind

type TyVar = TyVar of string * Kind

type TyExpr = TVarExpr of TyVar
            | TConExpr of TyCon
            | TApExpr of TyExpr * List<TyExpr>

// The third element of the parameter tuple (Lazy<string>) is the error message to show to the user
// in the event that an instance could not be located for this predicate
[<CustomEquality; CustomComparison>]
type Pred<'a> when 'a : equality and 'a : comparison = IsIn of (ModQualifierRec * List<'a> * Lazy<string>)
                                                             override x.Equals y =
                                                                 match y with
                                                                 | :? Pred<'a> as x' ->
                                                                     let (IsIn (n, t, _), IsIn(n', t', _)) = (x, x')
                                                                     (n, t) = (n', t')
                                                                 | _ -> false
                                                             override x.GetHashCode() =
                                                                 let (IsIn (n, t, e)) = x
                                                                 (n, t).GetHashCode()
                                                             interface System.IComparable with
                                                                 override x.CompareTo y =
                                                                     match y with
                                                                     | :? Pred<'a> as x' ->
                                                                         let (IsIn (n, t, _), IsIn(n', t', _)) = (x, x')
                                                                         let tup1 = (n, t)
                                                                         let tup2 = (n', t')
                                                                         compare tup1 tup2
                                                                     | _ ->
                                                                         invalidArg "y" "Cannot compare Pred to non-Pred type"

type Qual<'a, 'b> when 'a : equality and 'a : comparison = Qual of (Set<Pred<'a>> * 'b)
type Inst = Qual<TyExpr, Pred<TyExpr>>
type Class = Qual<TyVar, Pred<TyVar>>
type ClassEnv = Map<ModQualifierRec, Class>
type Subst = Map<TyVar, TyExpr>
type ConstrainedSubst = (Subst * Set<Pred<TyExpr>>)
type Scheme = Forall of (List<TyVar> * Qual<TyExpr, TyExpr>)

// Allows for module type to be used for declaring modules.
type Module = Module of Declaration list

and TyAdorn<'a> = (Position * Position) * Qual<TyExpr, TyExpr> * 'a

// Top level declarations
and FunctionRec = { name     : string;
                    scheme   : Scheme;
                    template : Template option;
                    clause   : FunctionClause }

and RecordRec =   { name     : string
                    fields   : (string * TyExpr) list;
                    template : Template option }

and ValueCon =    string * (TyExpr option)

and UnionRec =    { name     : string;
                    valCons  : ValueCon list;
                    template : Template option }

and LetDecRec =    { varName : string;
                     typ     : Qual<TyExpr, TyExpr>;
                     right   : TyAdorn<Expr>; }

and TypeclassFunc = { name : string;
                      scheme : Scheme;
                      template: Template option
                      returnType : TyExpr;
                      arguments :  (string * TyExpr) list; }

and TypeclassRec = { name : string;
                     class_ : Class;
                     functions : TypeclassFunc list }

and TypeclassInstanceRec = { instance : Inst;
                             functions : FunctionRec list }

// Declaration defined as any of the above.
and Declaration = FunctionDec   of FunctionRec
                | RecordDec     of RecordRec
                | UnionDec      of UnionRec
                | LetDec        of LetDecRec
                | ModuleNameDec of string
                | OpenDec       of string list
                | IncludeDec    of string list

// A template is associated with a function, record or union
and Template = TyVar list

// Use these to apply a template (ex: when calling a function with a template)
and TemplateApply = TyExpr list

and DeclarationTy = FunDecTy of Scheme
                  | RecordDecTy of TyVar list * Map<string, TyExpr>
                  | LetDecTy of TyExpr
                  | UnionDecTy of TyVar list * ModQualifierRec

// Pattern matching AST datatypes.
and MatchVarRec = { varName : string; mutable_ : bool; typ : TyExpr }
and MatchValConRec = { modQualifier : ModQualifierRec; innerPattern : TyAdorn<Pattern> option; id : int }
and MatchRecConRec = { typ : ModQualifierRec; fields : (string * TyAdorn<Pattern>) list }

and Pattern = MatchVar of MatchVarRec
            | MatchIntVal of int64
            | MatchFloatVal of float
            | MatchValCon of MatchValConRec
            | MatchRecCon of MatchRecConRec
            | MatchUnderscore
            | MatchTuple of TyAdorn<Pattern> list
            | MatchUnit
            | MatchTrue
            | MatchFalse

// Elements of a function clause.
and FunctionClause = {returnTy : TyExpr; arguments : (string * TyExpr) list; body : TyAdorn<Expr>}

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
and UnsafeTypeCastRec = { exp : TyAdorn<Expr>; typ : TyExpr }
// Function call/apply
and CallRec =         { func : TyAdorn<Expr>; args : TyAdorn<Expr> list }
// Applying the template of a function
and TemplateApplyExpRec = { func : Choice<string, ModQualifierRec>; templateArgs : TemplateApply }
and RecordExprRec =   { recordTy : ModQualifierRec; templateArgs : TemplateApply option; initFields : (string * TyAdorn<Expr>) list }
and ArrayMakeExpRec = { typ : TyExpr; initializer : TyAdorn<Expr> option }
and Expr = SequenceExp of TyAdorn<Expr> list
          | BinaryOpExp of BinaryOpRec
          | IfElseExp of IfElseRec
          | LetExp of LetRec
          | InternalDeclareVar of InternalDeclareVarExpRec // Only used internally for declaring variables
                                                           // that will actually be outputted by the compiler
          | InlineCode of string
          | AssignExp of AssignRec
          | ForLoopExp of ForLoopRec
          | WhileLoopExp of WhileLoopRec
          | DoWhileLoopExp of DoWhileLoopRec
          | CaseExp of CaseRec
          | UnaryOpExp of UnaryOpRec
          | RecordAccessExp of RecordAccessRec
          | ArrayAccessExp of ArrayAccessRec
          | VarExp of string * TyExpr list
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
          | ModQualifierExp of ModQualifierRec * TyExpr list
          | RecordExp of RecordExprRec
          | ArrayLitExp of TyAdorn<Expr> list
          | ArrayMakeExp of ArrayMakeExpRec
          | RefExp of TyAdorn<Expr>
          | TupleExp of TyAdorn<Expr> list
          | QuitExp of TyExpr
          | Smartpointer of string * TyAdorn<Expr>
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

let rec kindFun numTyArgs =
    match numTyArgs with
    | 0 -> Star
    | _ -> KFun ((List.replicate numTyArgs Star), Star)

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

let tFun tArgs tBody = TApExpr (TConExpr (TyCon (TyConFun, kindFun (List.length (tBody::tArgs)))), tBody::tArgs)

let tTuple tArgs = TApExpr (TConExpr (TyCon (TyConTuple, kindFun (List.length tArgs))), tArgs)

let tRef refTy = TApExpr (TConExpr (TyCon (TyConRef, KFun ([Star], Star))), [refTy])

let tArray elementTy capacityTy = TApExpr (TConExpr (TyCon (TyConArray, KFun ([Star; Star], Star))), [elementTy; capacityTy])

let tModuleQualifier modQual kind = TConExpr (TyCon (TyConUserDefined modQual, kind))

let modQualifierString {module_=module_; name=name} =
    module_ + ":" + name

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
    | TyConUserDefined modQual -> modQualifierString modQual
    // Higher kinded types cannot be printed without context of what they are parameterized by
    | (TyConArray | TyConFun | TyConRef | TyConTuple) ->
        let tyConName =
            match b with
            | TyConArray -> "array"
            | TyConFun -> "function"
            | TyConRef -> "ref"
            | TyConTuple -> "tuple"
            | _ -> raise <| ImpossibleInternalCompilerError "Failed to generate type constructor name when generating internal compiler error"
        raise <| InternalCompilerError (sprintf "Cannot convert %s constructor type to string without the context of its type parameters" tyConName)

let rec kindString k =
    match k with
    | Star -> "*"
    | KFun (kArgs, kRet) ->
        sprintf "(%s) -> %s" (List.map kindString kArgs |> String.concat ", ") (kindString kRet)

let tyVarString showKind (TyVar (name, kind)) =
    if showKind then
        sprintf "'%s : %s" name (kindString kind)
    else
        sprintf "'%s" name

let tyConString (TyCon (baseTyCon, _)) = baseTyConString baseTyCon

let tyExprString e =
    let rec tyExprString' addParens e' =
        let str =
            match e' with
            | TApExpr (TConExpr (TyCon (TyConRef, _)), [containedType]) ->
                sprintf "%s ref" (tyExprString' true containedType)
            | TApExpr (TConExpr (TyCon (TyConTuple, _)), tupleArgs) ->
                List.map (tyExprString' true) tupleArgs |> String.concat " * "
            | TApExpr (TConExpr (TyCon (TyConArray, _)), [containedType; capacityType]) ->
                sprintf "%s[%s]" (tyExprString' true containedType) (tyExprString' false capacityType)
            | TApExpr (TConExpr (TyCon (TyConFun, _)), retType::argTypes) ->
                let parensRetType =
                    match retType with
                    | TApExpr (TConExpr (TyCon (TyConFun, _)), _) -> false
                    | _ -> true
                sprintf "(%s) -> %s" (List.map (tyExprString' false) argTypes |> String.concat ", ") (tyExprString' parensRetType retType)
            | TConExpr (TyCon (baseTy, _)) ->
                baseTyConString baseTy
            | TVarExpr tv ->
                tyVarString false tv
            | TApExpr (tau, args) ->
                sprintf "%s<%s>" (tyExprString' true tau) (List.map (tyExprString' false) args |> String.concat ", ")
        match (e', addParens) with
        | (TApExpr _, true) ->
            sprintf "(%s)" str
        | _ ->
            str
    tyExprString' false e

let predicateString f (IsIn (path, tys, _)) =
    sprintf "%s<%s>" (modQualifierString path) (List.map f tys |> String.concat ", ")

let predicateTyExprString =
    predicateString (tyExprString)

let predicateTyVarString =
    predicateString (tyVarString false)

let qualString pstring tstring (Qual (predicates, tau)) =
    match Set.count predicates with
    | 0 -> tstring tau
    | _ -> sprintf "%s where %s" (tstring tau) (Set.map pstring predicates |> String.concat ", ")

let classString classDec =
    qualString predicateTyVarString predicateTyVarString classDec

let classEnvString classes =
    classes |>
    Map.toSeq |>
    Seq.map
        (fun (name, classInfo) ->
            sprintf "Class %s:\n%s" (modQualifierString name) (classString classInfo)) |>
    String.concat "\n\n"

let schemeString (Forall (tyvars, qual)) =
    sprintf "∀ %s . %s" (List.map (tyVarString false) tyvars |> String.concat " ") (qualString predicateTyExprString tyExprString qual)

// Takes in a wrapped AST object, returns the object within the TyAdorn.
let unwrap<'a> ((_, _, c) : TyAdorn<'a>) = c
let getType<'a> ((_, b, _) : TyAdorn<'a>) = b
let getPos<'a> ((a, _, _) : TyAdorn<'a>) = a

let dummyPos : Position = new Position("", -1L, -1L, -1L)

let dummyWrap<'a> c : TyAdorn<'a> = ((dummyPos, dummyPos), Qual (Set.empty, tUnit), c)

// Add typing to a TyAdorn.
let wrapWithType<'a> t c : TyAdorn<'a> = ((dummyPos, dummyPos), t, c)

let getQualPreds (Qual (preds, _)) = preds

let unwrapQual (Qual (_, x)) = x