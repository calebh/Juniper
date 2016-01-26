module Ast

type Module = Module of Declaration list

and FunctionRec = { name : string; clauses : FunctionClause list; template : Template}
and RecordRec =   { fields : (TyExpr * string) list; template : Template }
and ValueCon =    string * (TyExpr list)
and UnionRec =    { valCons : ValueCon list; template : Template }
and Declaration = FunctionDec of FunctionRec
                | RecordDec of RecordRec
                | Union of UnionRec

and TemplateRec = { tyVars : string list; capacityVars : string list}
and Template = Template of TemplateRec

and CapacityArithOp = PLUS | MINUS | MULTIPLY | DIVIDE
and CapacityOpRec = {op : CapacityArithOp; left : CapacityExpr; right : CapacityExpr }
and CapacityExpr = CapacityNameExpr of string
                 | CapacityOp of CapacityOpRec
                 | CapacityConst of int

and TyApplyRec = { name : string; args : TyExpr list }
and ArrayTyRec = { valueType : TyExpr; capacity : CapacityExpr }
and FunTyRec = { args : TyExpr list; returnType : TyExpr }
and TyExpr = Uint8
           | Uint16
           | Uint32
           | Uint64
           | Int8
           | Int16
           | Int32
           | Int64
           | TyName of string
           | TyVar of string
           | TyApply of TyApplyRec
           | ArrayTy of ArrayTyRec
           | FunTy of FunTyRec

// TODO
and Pattern = MatchVar of string
            | MatchVal

and FunctionClauseRec = {arguments : (Pattern * TyExpr) list; body : Expr}
and FunctionClause = FunctionClause of FunctionClauseRec

and SequenceRec =     { exps : Expr list }
and BinaryOpRec =     { op : BinaryOps; left : Expr; right : Expr }
and IfRec =           { condition : Expr; trueBranch : Expr }
and IfElseRec =       { condition : Expr; trueBranch : Expr; falseBranch : Expr }
and LetRec =          { varName : string; typ : TyExpr option; right : Expr }
and VarRec =          { varName : string; typ : TyExpr option; right : Expr }
and AssignRec =       { left : LeftAssign; right : Expr }
and ForLoopRec =      { init : Expr; condition : Expr; afterthought : Expr }
and WhileLoopRec =    { condition : Expr; body : Expr }
and DoWhileLoopRec =  { body: Expr; condition : Expr}
and MatchRec =        { on : Expr; clauses : (Pattern * Expr) list }
and UnaryOpRec =      { op : UnaryOps; exp : Expr }
and RecordAccessRec = { record : Expr; fieldName : string }
and LambdaRec =       { clauses : FunctionClause list }
and CallRec =         { func : Expr; templateArgs : Template; args : Expr list }
and Expr = SequenceExp of SequenceRec
          | BinaryOpExp of BinaryOpRec
          | IfExp of IfRec
          | IfElseExp of IfElseRec
          | LetExp of LetRec
          | VarExp of VarRec
          | AssignExp of AssignRec
          | ForLoopExp of ForLoopRec
          | WhileLoopExp of WhileLoopRec
          | DoWhileLoopExp of DoWhileLoopRec
          | MatchExp of MatchRec
          | UnaryOpExp of UnaryOpRec
          | RecordAccessExp of RecordAccessRec
          | UnitExp
          | LambdaExp of LambdaRec
          | IntExp of string
          | FloatExp of string
          | CallExp of CallRec
and BinaryOps = Add | Subtract | Multiply | Divide | BitwiseOr | BitwiseAnd | LogicalOr | LogicalAnd | Equal | NotEqual
and UnaryOps = LogicalNot | BitwiseNot

and VarMutationRec =    { varName : string }
and ArrayMutationRec =  { array : LeftAssign; index : Expr }
and RecordMutationRec = { record : LeftAssign; fieldName : string }
and LeftAssign = VarMutation of VarMutationRec
               | ArrayMutation of ArrayMutationRec
               | RecordMutation of RecordMutationRec