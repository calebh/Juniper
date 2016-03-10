module Ast

open Microsoft.FSharp.Text.Lexing

type Module = Module of PosAdorn<Declaration> list

// Tuple of starting position and ending position
and PosAdorn<'a> = (Position * Position) * TyExpr option * 'a

// Top level declarations
and FunctionRec = { name     : PosAdorn<string>; 
                    template : PosAdorn<Template> option;
                    clause   : PosAdorn<FunctionClause> }

and RecordRec =   { name     : PosAdorn<string>;
                    fields   : PosAdorn<(TyExpr * string) list>;
                    template : PosAdorn<Template> option }

and ValueCon =    PosAdorn<string> * PosAdorn<PosAdorn<TyExpr> list>
and UnionRec =    { name     : PosAdorn<string>;
                    valCons  : PosAdorn<ValueCon list>;
                    template : PosAdorn<Template> option }

and TypeAliasRec = { name       : PosAdorn<string>;
                     originalTy : PosAdorn<TyExpr>;
                     template   : PosAdorn<Template> option }

and LetDecRec = { varName : PosAdorn<string>;
                  typ     : PosAdorn<TyExpr>;
                  right   : PosAdorn<Expr>; }

and Declaration = FunctionDec   of FunctionRec
                | RecordDec     of RecordRec
                | UnionDec      of UnionRec
                | LetDec        of LetDecRec
                | ExportDec     of PosAdorn<PosAdorn<string> list>
                | ModuleNameDec of PosAdorn<string>
                | TypeAliasDec  of TypeAliasRec
                | OpenDec       of PosAdorn<PosAdorn<string> list>

// A template is associated with a function, record or union
and Template = { tyVars : PosAdorn<PosAdorn<string> list>; capVars : PosAdorn<PosAdorn<string> list> }

// Use these to apply a template (ex: when calling a function with a template)
and TemplateApply = { tyExprs : PosAdorn<PosAdorn<TyExpr> list>; capExprs : PosAdorn<PosAdorn<CapacityExpr> list> }

and CapacityArithOp = CAPPLUS | CAPMINUS | CAPMULTIPLY | CAPDIVIDE
and CapacityOpRec = { left : PosAdorn<CapacityExpr>; op : PosAdorn<CapacityArithOp>; right : PosAdorn<CapacityExpr> }
and CapacityExpr = CapacityNameExpr of PosAdorn<string>
                 | CapacityOp of CapacityOpRec
                 | CapacityConst of PosAdorn<string>

and TyApplyRec = { tyConstructor : PosAdorn<TyExpr>; args : PosAdorn<PosAdorn<TyExpr> list> }
and ArrayTyRec = { valueType : PosAdorn<TyExpr>; capacity : PosAdorn<CapacityExpr> }
and FunTyRec = { tyVarArity : PosAdorn<int>; capVarArity : PosAdorn<int>; args : PosAdorn<TyExpr> list; returnType : PosAdorn<TyExpr> }
and BaseTypes = TyUint8
              | TyUint16
              | TyUint32
              | TyUint64
              | TyInt8
              | TyInt16
              | TyInt32
              | TyInt64
              | TyBool
              | TyUnit
and TyExpr = BaseTy of PosAdorn<BaseTypes>
           | TyModuleQualifier of ModQualifierRec
           | TyName of PosAdorn<string>
           | TyApply of TyApplyRec
           | ArrayTy of ArrayTyRec
           | FunTy of FunTyRec
           | ForallTy of PosAdorn<string>

and Pattern = MatchVar of PosAdorn<string>
            | MatchModQualifier of ModQualifierRec
            | MatchIntVal of PosAdorn<string>
            | MatchFloatVal of PosAdorn<string>
            | MatchValCon of PosAdorn<string> * PosAdorn<PosAdorn<Pattern> list>
            | MatchValConModQualifier of PosAdorn<ModQualifierRec> * PosAdorn<PosAdorn<Pattern> list>
            | MatchRecCon of PosAdorn<string> * PosAdorn<(PosAdorn<string> * PosAdorn<Pattern>) list>
            | MatchRecConModQualifier of PosAdorn<ModQualifierRec> *  PosAdorn<(PosAdorn<string> * PosAdorn<Pattern>) list>
            | MatchUnderscore

and FunctionClause = {returnTy : PosAdorn<TyExpr>; arguments : PosAdorn<(PosAdorn<TyExpr> * PosAdorn<string>) list>; body : PosAdorn<Expr>}

and ModQualifierRec = { module_ : PosAdorn<string>; name : PosAdorn<string> }

and SequenceRec =     { exps : PosAdorn<PosAdorn<Expr> list> }
and BinaryOpRec =     { left : PosAdorn<Expr>; op : PosAdorn<BinaryOps>; right : PosAdorn<Expr> }
and IfElseRec =       { condition : PosAdorn<Expr>; trueBranch : PosAdorn<Expr>; falseBranch : PosAdorn<Expr> }
and LetRec =          { varName : PosAdorn<string>; typ : PosAdorn<TyExpr> option; right : PosAdorn<Expr>; mutable_ : PosAdorn<bool> }
and AssignRec =       { left : PosAdorn<LeftAssign>; right : PosAdorn<Expr> }
and ForLoopRec =      { typ : PosAdorn<TyExpr>; varName : PosAdorn<string>; start : PosAdorn<Expr>; end_ : PosAdorn<Expr>; body : PosAdorn<Expr> }
and WhileLoopRec =    { condition : PosAdorn<Expr>; body : PosAdorn<Expr> }
and DoWhileLoopRec =  { condition : PosAdorn<Expr>; body: PosAdorn<Expr> }
and CaseRec =         { on : PosAdorn<Expr>; clauses : PosAdorn<(PosAdorn<Pattern> * PosAdorn<Expr>) list> }
and UnaryOpRec =      { op : PosAdorn<UnaryOps>; exp : PosAdorn<Expr> }
and RecordAccessRec = { record : PosAdorn<Expr>; fieldName : PosAdorn<string> }
and ArrayAccessRec =  { array : PosAdorn<Expr>; index : PosAdorn<Expr> }
and VarExpRec =       { name : PosAdorn<string> }
and LambdaRec =       { clause : PosAdorn<FunctionClause> }
and CallRec =         { func : PosAdorn<Expr>; args : PosAdorn<PosAdorn<Expr> list> }
and TemplateApplyExpRec = { func : PosAdorn<Expr>; templateArgs : PosAdorn<TemplateApply> }
and RecordExprRec =   { recordTy : PosAdorn<TyExpr>; templateArgs : PosAdorn<TemplateApply> option; initFields : PosAdorn<(PosAdorn<string> * PosAdorn<Expr>) list> }
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
          | ListLitExp of PosAdorn<PosAdorn<Expr> list>
and BinaryOps = Add | Subtract | Multiply | Divide | Modulo | BitwiseOr | BitwiseAnd | LogicalOr | LogicalAnd | Equal | NotEqual | GreaterOrEqual | LessOrEqual | Greater | Less
and UnaryOps = LogicalNot | BitwiseNot

and VarMutationRec =    { varName : PosAdorn<string> }
and ArrayMutationRec =  { array : PosAdorn<LeftAssign>; index : PosAdorn<Expr> }
and RecordMutationRec = { record : PosAdorn<LeftAssign>; fieldName : PosAdorn<string> }
and LeftAssign = VarMutation of VarMutationRec
               | ArrayMutation of ArrayMutationRec
               | RecordMutation of RecordMutationRec

let unwrap<'a> ((_, _, c) : PosAdorn<'a>) = c
let dummyPos : Position = {pos_fname="dummy pos"
                           pos_lnum = -1
                           pos_bol = -1
                           pos_cnum = -1}
let dummyWrap<'a> c : PosAdorn<'a> = ((dummyPos, dummyPos), None, c)

let wrapWithType<'a> t c : PosAdorn<'a> = ((dummyPos, dummyPos), Some t, c)