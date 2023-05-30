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

and ConstraintType = IsNum of PosAdorn<unit>
                   | IsInt of PosAdorn<unit>
                   | IsReal of PosAdorn<unit>
                   | HasFields of PosAdorn<RecordRec>
                   | IsPacked of PosAdorn<unit>

and RecordRec = { packed : PosAdorn<unit> option;
                  fields : PosAdorn<(PosAdorn<string> * PosAdorn<TyExpr>) list>; }

// Top level declarations
and FunctionRec = { name     : PosAdorn<string>;
                    clause   : PosAdorn<FunctionClause> }

and AliasRec =   { name     : PosAdorn<string>;
                   template : Template option;
                   typ : PosAdorn<TyExpr> }

// Value constructor
and ValueCon =    PosAdorn<string> * (PosAdorn<TyExpr> list)

// Algrebraic datatype. Template is optional.
and AlgDataTypeRec = { name     : PosAdorn<string>;
                       valCons  : PosAdorn<ValueCon list>;
                       template : Template option }

// Let statement for functional-style declarations.
and LetDecRec = { varName : PosAdorn<string>;
                  typ     : PosAdorn<TyExpr> option;
                  right   : PosAdorn<Expr>; }

// Declaration defined as any of the above.
and Declaration = FunctionDec   of FunctionRec
                | AlgDataTypeDec of AlgDataTypeRec
                | AliasDec      of AliasRec
                | LetDec        of LetDecRec
                | ModuleNameDec of PosAdorn<string>
                | OpenDec       of PosAdorn<PosAdorn<string> list>
                | IncludeDec    of PosAdorn<PosAdorn<string> list>
                | InlineCodeDec of PosAdorn<string>

and Kind = StarKind of PosAdorn<unit>
         | IntKind of PosAdorn<unit>

// A template is associated with an algebraic datatype or alias
and Template = PosAdorn<(PosAdorn<string> * Kind) list>

// Use these to apply a template
and TemplateApply = PosAdorn<PosAdorn<TyExpr> list>

// Capacities are used for making lists and arrays of fixed maximum sizes.
// Due to the restrictions on the parsing process, capacities and type expressions are unified in this
// AST. Later on in the compilation process they become separated (in the typed AST)
and CapacityArithOp = CapAdd | CapSubtract | CapMultiply | CapDivide
and CapacityUnaryOp = CapNegate
and CapacityArithOpRec = { left : PosAdorn<TyExpr>; op : PosAdorn<CapacityArithOp>; right : PosAdorn<TyExpr> }
and CapacityUnaryOpRec = { op : PosAdorn<CapacityUnaryOp>; term : PosAdorn<TyExpr> }
                 

// The language is statically typed, and so there must be support for Type Expressons and their applications
// (applying a typed datatype, typed arrays, typed functions definitions, a list of base types).
and TyApplyRec = { tyConstructor : PosAdorn<TyExpr>; args : PosAdorn<TemplateApply> }
and ArrayTyRec = { valueType : PosAdorn<TyExpr>; capacity : PosAdorn<TyExpr> }
and FunTyRec = { closure : PosAdorn<TyExpr>; args : PosAdorn<TyExpr> list; returnType : PosAdorn<TyExpr> }
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
           | RefTy of PosAdorn<TyExpr>
           | TupleTy of PosAdorn<TyExpr> list
           | RecordTy of PosAdorn<RecordRec>
           | ClosureTy of PosAdorn<(PosAdorn<string> * PosAdorn<TyExpr>) list>
           | UnderscoreTy of PosAdorn<unit>
           | CapacityOp of CapacityArithOpRec
           | CapacityUnaryOp of CapacityUnaryOpRec
           | CapacityConst of PosAdorn<int64>

// Pattern matching AST datatypes.
and MatchVarRec = {varName : PosAdorn<string>; mutable_ : PosAdorn<bool>; typ : PosAdorn<TyExpr> option}
and MatchValConRec = { name : PosAdorn<Choice<string, ModQualifierRec>>; innerPattern : PosAdorn<PosAdorn<Pattern> list> }

and Pattern = MatchVar of MatchVarRec
            | MatchIntVal of PosAdorn<int64>
            | MatchFloatVal of PosAdorn<string>
            | MatchValCon of MatchValConRec
            | MatchRecCon of PosAdorn<(PosAdorn<string> * PosAdorn<Pattern>) list>
            | MatchUnderscore of PosAdorn<unit>
            | MatchTuple of PosAdorn<PosAdorn<Pattern> list>
            | MatchUnit of PosAdorn<unit>
            | MatchTrue of PosAdorn<unit>
            | MatchFalse of PosAdorn<unit>

// Elements of a function clause.
and FunctionClause = {returnTy : PosAdorn<TyExpr> option; arguments : PosAdorn<(PosAdorn<string> * (PosAdorn<TyExpr> option)) list>; body : PosAdorn<Expr>; interfaceConstraints : PosAdorn<PosAdorn<PosAdorn<TyExpr> * PosAdorn<ConstraintType>> list>}

// Module qualifier.
and ModQualifierRec = { module_ : PosAdorn<string>; name : PosAdorn<string> }

// Other AST objects and their definitions. Most of them are explained within their names.
// Binary operation
and BinaryOpRec =     { left : PosAdorn<Expr>; op : PosAdorn<BinaryOps>; right : PosAdorn<Expr> }
and IfElseRec =       { condition : PosAdorn<Expr>; trueBranch : PosAdorn<Expr>; falseBranch : PosAdorn<Expr> }
and IfRec =           { condition : PosAdorn<Expr>; trueBranch : PosAdorn<Expr> }
and LetRec =          { left : PosAdorn<Pattern>; right : PosAdorn<Expr> }
// Variable assign
and AssignRec =       { left : PosAdorn<LeftAssign>; right : PosAdorn<Expr>; }
and ForInLoopRec =      { typ : PosAdorn<TyExpr> option; varName : PosAdorn<string>; start : PosAdorn<Expr>; end_ : PosAdorn<Expr>; body : PosAdorn<Expr> }
and ForLoopRec =      { initLoop : PosAdorn<Expr>; loopCondition : PosAdorn<Expr>; loopStep : PosAdorn<Expr>; body : PosAdorn<Expr> }
and WhileLoopRec =    { condition : PosAdorn<Expr>; body : PosAdorn<Expr> }
and DoWhileLoopRec =  { condition : PosAdorn<Expr>; body: PosAdorn<Expr> }
// Pattern matching
and CaseRec =         { on : PosAdorn<Expr>; clauses : PosAdorn<(PosAdorn<Pattern> * PosAdorn<Expr>) list> }
// Unary operation
and UnaryOpRec =      { op : PosAdorn<UnaryOps>; exp : PosAdorn<Expr> }
and RecordAccessRec = { record : PosAdorn<Expr>; fieldName : PosAdorn<string> }
and RefRecordAccessRec = { recordRef : PosAdorn<Expr>; fieldName : PosAdorn<string> }
and ArrayAccessRec =  { array : PosAdorn<Expr>; index : PosAdorn<Expr> }
and InternalDeclareVarExpRec = { varName : PosAdorn<string>; typ : PosAdorn<TyExpr> option; right : PosAdorn<Expr> }
and InternalValConAccessRec = { valCon : PosAdorn<Expr>; typ : PosAdorn<TyExpr> }
and InternalTupleAccessRec = { tuple : PosAdorn<Expr>; index : int }
// Function call/apply
and CallRec =         { func : PosAdorn<Expr>; args : PosAdorn<PosAdorn<Expr> list> }
and RecordExprRec =   { packed : PosAdorn<unit> option; initFields : PosAdorn<(PosAdorn<string> * PosAdorn<Expr>) list> }
and ArrayMakeExpRec = { typ : PosAdorn<TyExpr>; initializer : PosAdorn<Expr> option }
and TypeConstraintRec = { exp : PosAdorn<Expr>; typ : PosAdorn<TyExpr> }
and DeclVarExpRec = { varName : PosAdorn<string>; typ : PosAdorn<TyExpr> }
and Expr = SequenceExp of PosAdorn<PosAdorn<Expr> list>
          | BinaryOpExp of BinaryOpRec
          | IfElseExp of IfElseRec
          | IfExp of IfRec
          | LetExp of LetRec
          | InlineCode of PosAdorn<string>
          | AssignExp of AssignRec
          | ForInLoopExp of ForInLoopRec
          | ForLoopExp of ForLoopRec
          | WhileLoopExp of WhileLoopRec
          | DoWhileLoopExp of DoWhileLoopRec
          | CaseExp of CaseRec
          | UnaryOpExp of UnaryOpRec
          | RecordAccessExp of RecordAccessRec
          | RefRecordAccessExp of RefRecordAccessRec
          | ArrayAccessExp of ArrayAccessRec
          | VarExp of PosAdorn<string>
          | DeclVarExp of DeclVarExpRec
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
          | FloatExp of PosAdorn<string>
          | DoubleExp of PosAdorn<string>
          | CharListLiteral of PosAdorn<string>
          | StringLiteral of PosAdorn<string>
          | CallExp of CallRec
          | ModQualifierExp of PosAdorn<ModQualifierRec>
          | RecordExp of RecordExprRec
          | ArrayLitExp of PosAdorn<PosAdorn<Expr> list>
          | ArrayMakeExp of ArrayMakeExpRec
          | RefExp of PosAdorn<Expr>
          | TupleExp of PosAdorn<Expr> list
          | QuitExp of PosAdorn<TyExpr> option
          | TypeConstraint of TypeConstraintRec
          | Smartpointer of PosAdorn<Expr> * PosAdorn<Expr>
          | NullExp of PosAdorn<unit>
          | SizeofExp of PosAdorn<TyExpr>
and BinaryOps = Add | Subtract | Multiply | Divide | Modulo | BitwiseOr | BitwiseAnd | BitwiseXor
              | LogicalOr | LogicalAnd | Equal | NotEqual | GreaterOrEqual | LessOrEqual | Greater | Less
              | BitshiftLeft | BitshiftRight | Pipe
and UnaryOps = LogicalNot | BitwiseNot | Negate | Deref

// Mutations are changes in already declared variables, arrays, records, etc.
and ArrayMutationRec =  { array : PosAdorn<LeftAssign>; index : PosAdorn<Expr> }
and RecordMutationRec = { record : PosAdorn<LeftAssign>; fieldName : PosAdorn<string> }
and RefRecordMutationRec = { recordRef : PosAdorn<Expr>; fieldName : PosAdorn<string> }
and LeftAssign = VarMutation of PosAdorn<string>
               | ModQualifierMutation of PosAdorn<ModQualifierRec>
               | ArrayMutation of ArrayMutationRec
               | RecordMutation of RecordMutationRec
               | RefRecordMutation of RefRecordMutationRec
               | RefMutation of PosAdorn<Expr>

// Takes in a wrapped AST object, returns the object within the PosAdorn.
let unwrap<'a> ((_, c) : PosAdorn<'a>) = c
// Takes in a wrapped AST object, returns the starting position.
let getPos<'a> ((a, _) : PosAdorn<'a>) = a