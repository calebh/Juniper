module Ast

type Module = Module of Declaration list

and FunctionRec = { name : string; template : Template option; clause : FunctionClause; returnTy : TyExpr}
and RecordRec =   { name : string; fields : (TyExpr * string) list; template : Template }
and ValueCon =    string * (TyExpr list)
and UnionRec =    { name : string; valCons : ValueCon list; template : Template }
and Declaration = FunctionDec of FunctionRec
                | RecordDec of RecordRec
                | UnionDec of UnionRec
                | Export of string list
                | Module of string 

and TemplateRec = { tyVars : string list; capacityVars : string list}
and Template = Template of TemplateRec

and CapacityArithOp = PLUS | MINUS | MULTIPLY | DIVIDE
and CapacityOpRec = {op : CapacityArithOp; left : CapacityExpr; right : CapacityExpr }
and CapacityExpr = CapacityNameExpr of string
                 | CapacityOp of CapacityOpRec
                 | CapacityConst of int

and TyApplyRec = { tyConstructor : TyExpr; args : TyExpr list }
and ArrayTyRec = { valueType : TyExpr; capacity : CapacityExpr }
and FunTyRec = { args : TyExpr list; returnType : TyExpr }
and TyModQualifierRec = { module_ : string; name : string }
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
           | TyModuleQualifier of TyModQualifierRec
           | TyName of string
           | TyVar of string
           | TyApply of TyApplyRec
           | ArrayTy of ArrayTyRec
           | FunTy of FunTyRec

and Pattern = MatchVar of string
            | MatchIntVal of string
            | MatchFloatVal of string
            | MatchValCon of string * (Pattern list)
            | MatchUnderscore

and FunctionClauseRec = {arguments : (TyExpr * string) list; body : Expr}
and FunctionClause = FunctionClause of FunctionClauseRec

and SequenceRec =     { exps : Expr list }
and BinaryOpRec =     { op : BinaryOps; left : Expr; right : Expr }
and IfRec =           { condition : Expr; trueBranch : Expr }
and IfElseRec =       { condition : Expr; trueBranch : Expr; falseBranch : Expr }
and DecLetRec =       { varName : string; typ : TyExpr option; right : Expr }
and DecVarRec =       { varName : string; typ : TyExpr option; right : Expr }
and AssignRec =       { left : LeftAssign; right : Expr }
and ForLoopRec =      { init : Expr; condition : Expr; afterthought : Expr }
and WhileLoopRec =    { condition : Expr; body : Expr }
and DoWhileLoopRec =  { body: Expr; condition : Expr }
and MatchRec =        { on : Expr; clauses : (Pattern * Expr) list }
and UnaryOpRec =      { op : UnaryOps; exp : Expr }
and RecordAccessRec = { record : Expr; fieldName : string }
and ArrayAccessRec =  { array : Expr; index : Expr }
and VarExpRec =       { name : string }
and LambdaRec =       { clause : FunctionClause }
and CallRec =         { func : Expr; templateArgs : Template option; args : Expr list }
and ModQualifierRec = { module_ : string; name : string }
and Expr = SequenceExp of SequenceRec
          | BreakExp
          | BinaryOpExp of BinaryOpRec
          | IfExp of IfRec
          | IfElseExp of IfElseRec
          | DecLetExp of DecLetRec
          | DecVarExp of DecVarRec
          | AssignExp of AssignRec
          | ForLoopExp of ForLoopRec
          | WhileLoopExp of WhileLoopRec
          | DoWhileLoopExp of DoWhileLoopRec
          | MatchExp of MatchRec
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
          | ModuleQualifier of ModQualifierRec
and BinaryOps = Add | Subtract | Multiply | Divide | BitwiseOr | BitwiseAnd | LogicalOr | LogicalAnd | Equal | NotEqual
and UnaryOps = LogicalNot | BitwiseNot

and VarMutationRec =    { varName : string }
and ArrayMutationRec =  { array : LeftAssign; index : Expr }
and RecordMutationRec = { record : LeftAssign; fieldName : string }
and LeftAssign = VarMutation of VarMutationRec
               | ArrayMutation of ArrayMutationRec
               | RecordMutation of RecordMutationRec