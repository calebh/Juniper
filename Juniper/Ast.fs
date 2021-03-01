module Ast
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
                    packed   : PosAdorn<unit> option
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
                | InlineCodeDec of PosAdorn<string>

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
              | TyString
              | TyRawPointer
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
and UnsafeTypeCastRec = { exp : PosAdorn<Expr>; typ : PosAdorn<TyExpr> }
and DeclVarExpRec = { varName : PosAdorn<string>; typ : PosAdorn<TyExpr> }
and Expr = SequenceExp of PosAdorn<PosAdorn<Expr> list>
          | BinaryOpExp of BinaryOpRec
          | IfElseExp of IfElseRec
          | LetExp of LetRec
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
          | DeclVarExp of DeclVarExpRec
          | UnsafeTypeCast of UnsafeTypeCastRec
          | UnitExp of PosAdorn<unit>
          | TrueExp of PosAdorn<unit>
          | FalseExp of PosAdorn<unit>
          | LambdaExp of PosAdorn<FunctionClause>
          | IntExp of PosAdorn<int64>
          | Int8Exp of PosAdorn<int64>
          | UInt8Exp of PosAdorn<int64>
          | Int16Exp of PosAdorn<int64>
          | UInt16Exp of PosAdorn<int64>
          | Int32Exp of PosAdorn<int64>
          | UInt32Exp of PosAdorn<int64>
          | Int64Exp of PosAdorn<int64>
          | UInt64Exp of PosAdorn<int64>
          | FloatExp of PosAdorn<float>
          | DoubleExp of PosAdorn<float>
          | CharListLiteral of PosAdorn<string>
          | StringLiteral of PosAdorn<string>
          | CallExp of CallRec
          | TemplateApplyExp of TemplateApplyExpRec
          | ModQualifierExp of PosAdorn<ModQualifierRec>
          | RecordExp of RecordExprRec
          | ArrayLitExp of PosAdorn<PosAdorn<Expr> list>
          | ArrayMakeExp of ArrayMakeExpRec
          | RefExp of PosAdorn<Expr>
          | TupleExp of PosAdorn<Expr> list
          | QuitExp of PosAdorn<TyExpr> option
          | TypeConstraint of TypeConstraintRec
          | Smartpointer of PosAdorn<Expr>
          | NullExp of PosAdorn<unit>
and BinaryOps = Add | Subtract | Multiply | Divide | Modulo | BitwiseOr | BitwiseAnd | BitwiseXor
              | LogicalOr | LogicalAnd | Equal | NotEqual | GreaterOrEqual | LessOrEqual | Greater | Less
              | BitshiftLeft | BitshiftRight | Pipe
and UnaryOps = LogicalNot | BitwiseNot | Negate | Deref

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