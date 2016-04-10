module Ast

open Microsoft.FSharp.Text.Lexing

// Allows for module type to be used for declaring modules.
type Module = Module of PosAdorn<Declaration> list

// Tuple of starting position and ending position
// Note: The 'option' keyword indicates that field is optional (can have 'none' as assignment)

// PosAdorn wraps a an AST object in a start and end line position for helpful debugging
// messages. It also includes the type of the object, which starts as 'none'.
// Virtually every object in the AST is a PosAdorn wrapping another object.
and PosAdorn<'a> = (Position * Position) * TyExpr option * 'a

// Top level declarations
// Function object. Template is optional.
and FunctionRec = { name     : PosAdorn<string>;
                    template : PosAdorn<Template> option;
                    clause   : PosAdorn<FunctionClause> }

// Record object. Template is optional.
and RecordRec =   { name     : PosAdorn<string>;
                    fields   : PosAdorn<(TyExpr * string) list>;
                    template : PosAdorn<Template> option }

// Value constructor. Type is optional.
and ValueCon =    PosAdorn<string> * (PosAdorn<TyExpr> option)

// Union algrebraic datatype. Template is optional.
and UnionRec =    { name     : PosAdorn<string>;
                    valCons  : PosAdorn<ValueCon list>;
                    template : PosAdorn<Template> option }

// Let statement for functional-style declarations.
and LetDecRec = { varName : PosAdorn<string>;
                  typ     : PosAdorn<TyExpr>;
                  right   : PosAdorn<Expr>; }

// Declaration defined as any of the above.
and Declaration = FunctionDec   of FunctionRec
                | RecordDec     of RecordRec
                | UnionDec      of UnionRec
                | LetDec        of LetDecRec
                | ExportDec     of PosAdorn<PosAdorn<string> list>
                | ModuleNameDec of PosAdorn<string>
                | OpenDec       of PosAdorn<PosAdorn<string> list>

// A template is associated with a function, record or union
and Template = { tyVars : PosAdorn<PosAdorn<string> list>; capVars : PosAdorn<PosAdorn<string> list> }

// Use these to apply a template (ex: when calling a function with a template)
and TemplateApply = { tyExprs : PosAdorn<PosAdorn<TyExpr> list>; capExprs : PosAdorn<PosAdorn<CapacityExpr> list> }

// Capacities are used for making lists and arrays of fixed maximum sizes.
and CapacityArithOp = CAPPLUS | CAPMINUS | CAPMULTIPLY | CAPDIVIDE
and CapacityOpRec = { left : PosAdorn<CapacityExpr>; op : PosAdorn<CapacityArithOp>; right : PosAdorn<CapacityExpr> }
and CapacityExpr = CapacityNameExpr of PosAdorn<string>
                 | CapacityOp of CapacityOpRec
                 | CapacityConst of PosAdorn<string>

// The language is statically typed, and so there must be support for Type Expressons and their applications
// (applying a typed datatype, typed arrays, typed functions definitions, a list of base types).
and TyApplyRec = { tyConstructor : PosAdorn<TyExpr>; args : PosAdorn<TemplateApply> }
and ArrayTyRec = { valueType : PosAdorn<TyExpr>; capacity : PosAdorn<CapacityExpr> }
and FunTyRec = { template : PosAdorn<Template> option; source : ModQualifierRec option; args : PosAdorn<TyExpr> list; returnType : PosAdorn<TyExpr> }
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
           | TyModuleQualifier of ModQualifierRec
           | TyName of PosAdorn<string>
           | TyApply of TyApplyRec
           | ArrayTy of ArrayTyRec
           | FunTy of FunTyRec
           | ForallTy of PosAdorn<string>
           | RefTy of PosAdorn<TyExpr>
           | TupleTy of PosAdorn<TyExpr> list

// Pattern matching AST datatypes.
and MatchVarRec = {varName : PosAdorn<string>; mutable_ : PosAdorn<bool>; typ : PosAdorn<TyExpr> option}
and MatchValConRec = { name : PosAdorn<string>; template : PosAdorn<TemplateApply> option; innerPattern : PosAdorn<Pattern>; id : int option }
and MatchValConModQualifierRec = { modQualifier : PosAdorn<ModQualifierRec>; template : PosAdorn<TemplateApply> option; innerPattern : PosAdorn<Pattern>; id : int option }
and MatchRecConRec = { typ : PosAdorn<TyExpr>; fields : PosAdorn<(PosAdorn<string> * PosAdorn<Pattern>) list> }

and Pattern = MatchVar of MatchVarRec
            | MatchIntVal of PosAdorn<string>
            | MatchFloatVal of PosAdorn<string>
            | MatchValCon of MatchValConRec
            | MatchValConModQualifier of MatchValConModQualifierRec
            | MatchRecCon of MatchRecConRec
            | MatchUnderscore
            | MatchTuple of PosAdorn<PosAdorn<Pattern> list>
            | MatchEmpty

// Elements of a function clause.
and FunctionClause = {returnTy : PosAdorn<TyExpr>; arguments : PosAdorn<(PosAdorn<TyExpr> * PosAdorn<string>) list>; body : PosAdorn<Expr>}

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
and ForLoopRec =      { typ : PosAdorn<TyExpr>; varName : PosAdorn<string>; start : PosAdorn<Expr>; direction : PosAdorn<Direction>; end_ : PosAdorn<Expr>; body : PosAdorn<Expr> }
and WhileLoopRec =    { condition : PosAdorn<Expr>; body : PosAdorn<Expr> }
and DoWhileLoopRec =  { condition : PosAdorn<Expr>; body: PosAdorn<Expr> }
// Pattern matching
and CaseRec =         { on : PosAdorn<Expr>; clauses : PosAdorn<(PosAdorn<Pattern> * PosAdorn<Expr>) list> }
// Unary operation
and UnaryOpRec =      { op : PosAdorn<UnaryOps>; exp : PosAdorn<Expr> }
and RecordAccessRec = { record : PosAdorn<Expr>; fieldName : PosAdorn<string> }
and ArrayAccessRec =  { array : PosAdorn<Expr>; index : PosAdorn<Expr> }
and VarExpRec =       { name : PosAdorn<string> }
// Lambda function
and LambdaRec =       { clause : PosAdorn<FunctionClause> }
and InternalDeclareVarExpRec = { varName : PosAdorn<string>; typ : PosAdorn<TyExpr> option; right : PosAdorn<Expr> }
and InternalValConAccessRec = { valCon : PosAdorn<Expr>; typ : PosAdorn<TyExpr> }
and InternalTupleAccessRec = { tuple : PosAdorn<Expr>; index : int }
// Function call/apply
and CallRec =         { func : PosAdorn<Expr>; args : PosAdorn<PosAdorn<Expr> list> }
// Applying the template of a function
and TemplateApplyExpRec = { func : PosAdorn<Expr>; templateArgs : PosAdorn<TemplateApply> }
and RecordExprRec =   { recordTy : PosAdorn<TyExpr>; templateArgs : PosAdorn<TemplateApply> option; initFields : PosAdorn<(PosAdorn<string> * PosAdorn<Expr>) list> }
and ArrayMakeExpRec = { typ : PosAdorn<TyExpr>; initializer : PosAdorn<Expr> option }
and Expr = SequenceExp of PosAdorn<PosAdorn<Expr> list>
          | BinaryOpExp of BinaryOpRec
          | IfElseExp of IfElseRec
          | LetExp of LetRec
          | InternalDeclareVar of InternalDeclareVarExpRec // Only used internally for declaring variables
                                                           // that will actually be outputted by the compiler
          | InternalValConAccess of InternalValConAccessRec // Only used internally for type checking pattern
                                                            // matching. Essentially acts like a type cast
          | InternalTupleAccess of InternalTupleAccessRec
          | InlineCode of PosAdorn<string>
          | AssignExp of AssignRec
          | ForLoopExp of ForLoopRec
          | WhileLoopExp of WhileLoopRec
          | DoWhileLoopExp of DoWhileLoopRec
          | CaseExp of CaseRec
          | UnaryOpExp of UnaryOpRec
          | RecordAccessExp of RecordAccessRec
          | ArrayAccessExp of ArrayAccessRec
          | VarExp of VarExpRec
          | UnitExp of PosAdorn<unit>
          | TrueExp of PosAdorn<unit>
          | FalseExp of PosAdorn<unit>
          | LambdaExp of LambdaRec
          | IntExp of PosAdorn<string>
          | FloatExp of PosAdorn<string>
          | CallExp of CallRec
          | TemplateApplyExp of TemplateApplyExpRec
          | ModQualifierExp of ModQualifierRec
          | RecordExp of RecordExprRec
          | ArrayLitExp of PosAdorn<PosAdorn<Expr> list>
          | ArrayMakeExp of ArrayMakeExpRec
          | RefExp of PosAdorn<Expr>
          | DerefExp of PosAdorn<Expr>
          | TupleExp of PosAdorn<Expr> list
          | NullExp of PosAdorn<unit>
and BinaryOps = Add | Subtract | Multiply | Divide | Modulo | BitwiseOr | BitwiseAnd
              | LogicalOr | LogicalAnd | Equal | NotEqual | GreaterOrEqual | LessOrEqual | Greater | Less
              | BitshiftLeft | BitshiftRight
and UnaryOps = LogicalNot | BitwiseNot

// Mutations are changes in already declared variables, arrays, records, etc.
and VarMutationRec =    { varName : PosAdorn<string> }
and ArrayMutationRec =  { array : PosAdorn<LeftAssign>; index : PosAdorn<Expr> }
and RecordMutationRec = { record : PosAdorn<LeftAssign>; fieldName : PosAdorn<string> }
and ModQualifierMutationRec = { modQualifier : PosAdorn<ModQualifierRec> }
and LeftAssign = VarMutation of VarMutationRec
               | ModQualifierMutation of ModQualifierMutationRec
               | ArrayMutation of ArrayMutationRec
               | RecordMutation of RecordMutationRec

// Takes in a wrapped AST object, returns the object within the PosAdorn.
let unwrap<'a> ((_, _, c) : PosAdorn<'a>) = c
// Takes in a wrapped AST object, returns the starting position.
let getPos<'a> ((a, _, _) : PosAdorn<'a>) = a
// Takes in a wrapped AST object, returns the ending position.
let getType<'a> ((_, b, _) : PosAdorn<'a>) = b
// Dummy position used for initializing positions on PosAdorns
let dummyPos : Position = {pos_fname=""
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
    {tyExprs=tyExprs; capExprs=capExprs}
