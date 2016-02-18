module Ast

type Module = Module of Declaration list

// Top level declarations
and FunctionRec = { name : string; template : Template option; clause : FunctionClause; returnTy : TyExpr}
and RecordRec =   { name : string; fields : (TyExpr * string) list; template : Template option }
and ValueCon =    string * (TyExpr list)
and UnionRec =    { name : string; valCons : ValueCon list; template : Template option }
and TypeAliasRec = { name : string; originalTy : TyExpr; template : Template option }
and Declaration = FunctionDec of FunctionRec
                | RecordDec of RecordRec
                | UnionDec of UnionRec
                | LetDec of LetRec
                | Export of string list
                | ModuleNameDec of string
                | TypeAliasDec of TypeAliasRec
                | OpenDec of string list

// A template is associated with a function, record or union
and TemplateRec = { tyVars : string list; capVars : string list }
and Template = Template of TemplateRec

// Use these to apply a template (ex: when calling a function with a template)
and TemplateApplyRec = { tyExprs : TyExpr list; capExprs : CapacityExpr list }
and TemplateApply = TemplateApply of TemplateApplyRec

and CapacityArithOp = CAPPLUS | CAPMINUS | CAPMULTIPLY | CAPDIVIDE
and CapacityOpRec = { left : CapacityExpr; op : CapacityArithOp; right : CapacityExpr }
and CapacityExpr = CapacityNameExpr of string
                 | CapacityOp of CapacityOpRec
                 | CapacityConst of string

and TyApplyRec = { tyConstructor : TyExpr; args : TyExpr list }
and ArrayTyRec = { valueType : TyExpr; capacity : CapacityExpr }
and FunTyRec = { args : TyExpr list; returnType : TyExpr }
and BaseTypes = TyUint8
              | TyUint16
              | TyUint32
              | TyUint64
              | TyInt8
              | TyInt16
              | TyInt32
              | TyInt64
              | TyBool
and TyExpr = BaseTy of BaseTypes
           | TyModuleQualifier of ModQualifierRec
           | TyName of string
           | TyApply of TyApplyRec
           | ArrayTy of ArrayTyRec
           | FunTy of FunTyRec

and Pattern = MatchVar of string
            | MatchModQualifier of ModQualifierRec
            | MatchIntVal of string
            | MatchFloatVal of string
            | MatchValCon of string * (Pattern list)
            | MatchValConModQualifier of ModQualifierRec * (Pattern list)
            | MatchRecCon of string * ((string * Pattern) list)
            | MatchRecConModQualifier of ModQualifierRec * ((string * Pattern) list)
            | MatchUnderscore

and FunctionClauseRec = {arguments : (TyExpr * string) list; body : Expr}
and FunctionClause = FunctionClause of FunctionClauseRec

and ModQualifierRec = { module_ : string; name : string }

and SequenceRec =     { exps : Expr list }
and BinaryOpRec =     { op : BinaryOps; left : Expr; right : Expr }
and IfElseRec =       { condition : Expr; trueBranch : Expr; falseBranch : Expr }
and LetRec =          { varName : string; typ : TyExpr option; right : Expr; mutable_ : bool }
and AssignRec =       { left : LeftAssign; right : Expr }
and ForLoopRec =      { init : Expr; condition : Expr; afterthought : Expr }
and WhileLoopRec =    { condition : Expr; body : Expr }
and DoWhileLoopRec =  { condition : Expr; body: Expr }
and CaseRec =         { on : Expr; clauses : (Pattern * Expr) list }
and UnaryOpRec =      { op : UnaryOps; exp : Expr }
and RecordAccessRec = { record : Expr; fieldName : string }
and ArrayAccessRec =  { array : Expr; index : Expr }
and VarExpRec =       { name : string }
and LambdaRec =       { clause : FunctionClause; returnTy : TyExpr }
and CallRec =         { func : Expr; templateArgs : TemplateApply option; args : Expr list }
and RecordExprRec =   { recordTy : TyExpr; templateArgs : TemplateApply option; initFields : (string * Expr) list }
and Expr = SequenceExp of SequenceRec
          | BreakExp
          | BinaryOpExp of BinaryOpRec
          | IfElseExp of IfElseRec
          | LetExp of LetRec
          | AssignExp of AssignRec
          | ForLoopExp of ForLoopRec
          | WhileLoopExp of WhileLoopRec
          | DoWhileLoopExp of DoWhileLoopRec
          | CaseExp of CaseRec
          | UnaryOpExp of UnaryOpRec
          | RecordAccessExp of RecordAccessRec
          | ArrayAccessExp of ArrayAccessRec
          | VarExp of VarExpRec
          | UnitExp
          | TrueExp
          | FalseExp
          | LambdaExp of LambdaRec
          | IntExp of string
          | FloatExp of string
          | CallExp of CallRec
          | ModQualifierExp of ModQualifierRec
          | RecordExp of RecordExprRec
          | ListLitExp of Expr list
and BinaryOps = Add | Subtract | Multiply | Divide | Modulo | BitwiseOr | BitwiseAnd | LogicalOr | LogicalAnd | Equal | NotEqual | GreaterOrEqual | LessOrEqual | Greater | Less
and UnaryOps = LogicalNot | BitwiseNot

and VarMutationRec =    { varName : string }
and ArrayMutationRec =  { array : LeftAssign; index : Expr }
and RecordMutationRec = { record : LeftAssign; fieldName : string }
and LeftAssign = VarMutation of VarMutationRec
               | ArrayMutation of ArrayMutationRec
               | RecordMutation of RecordMutationRec