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

and ValueCon =    PosAdorn<string> * (PosAdorn<TyExpr> option)
and UnionRec =    { name     : PosAdorn<string>;
                    valCons  : PosAdorn<ValueCon list>;
                    template : PosAdorn<Template> option }

and LetDecRec = { varName : PosAdorn<string>;
                  typ     : PosAdorn<TyExpr>;
                  right   : PosAdorn<Expr>; }

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

and CapacityArithOp = CAPPLUS | CAPMINUS | CAPMULTIPLY | CAPDIVIDE
and CapacityOpRec = { left : PosAdorn<CapacityExpr>; op : PosAdorn<CapacityArithOp>; right : PosAdorn<CapacityExpr> }
and CapacityExpr = CapacityNameExpr of PosAdorn<string>
                 | CapacityOp of CapacityOpRec
                 | CapacityConst of PosAdorn<string>

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
              | TyBool
              | TyUnit
and TyExpr = BaseTy of PosAdorn<BaseTypes>
           | TyModuleQualifier of ModQualifierRec
           | TyName of PosAdorn<string>
           | TyApply of TyApplyRec
           | ArrayTy of ArrayTyRec
           | FunTy of FunTyRec
           | ForallTy of PosAdorn<string>
           | RefTy of PosAdorn<TyExpr>
           | TupleTy of PosAdorn<TyExpr> list

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

and FunctionClause = {returnTy : PosAdorn<TyExpr>; arguments : PosAdorn<(PosAdorn<TyExpr> * PosAdorn<string>) list>; body : PosAdorn<Expr>}

and ModQualifierRec = { module_ : PosAdorn<string>; name : PosAdorn<string> }

and Direction = Upto
              | Downto

and BinaryOpRec =     { left : PosAdorn<Expr>; op : PosAdorn<BinaryOps>; right : PosAdorn<Expr> }
and IfElseRec =       { condition : PosAdorn<Expr>; trueBranch : PosAdorn<Expr>; falseBranch : PosAdorn<Expr> }
and LetRec =          { left : PosAdorn<Pattern>; right : PosAdorn<Expr> }
and AssignRec =       { left : PosAdorn<LeftAssign>; right : PosAdorn<Expr>; ref : PosAdorn<bool> }
and ForLoopRec =      { typ : PosAdorn<TyExpr>; varName : PosAdorn<string>; start : PosAdorn<Expr>; direction : PosAdorn<Direction>; end_ : PosAdorn<Expr>; body : PosAdorn<Expr> }
and WhileLoopRec =    { condition : PosAdorn<Expr>; body : PosAdorn<Expr> }
and DoWhileLoopRec =  { condition : PosAdorn<Expr>; body: PosAdorn<Expr> }
and CaseRec =         { on : PosAdorn<Expr>; clauses : PosAdorn<(PosAdorn<Pattern> * PosAdorn<Expr>) list> }
and UnaryOpRec =      { op : PosAdorn<UnaryOps>; exp : PosAdorn<Expr> }
and RecordAccessRec = { record : PosAdorn<Expr>; fieldName : PosAdorn<string> }
and ArrayAccessRec =  { array : PosAdorn<Expr>; index : PosAdorn<Expr> }
and VarExpRec =       { name : PosAdorn<string> }
and LambdaRec =       { clause : PosAdorn<FunctionClause> }
and InternalDeclareVarExpRec = { varName : PosAdorn<string>; typ : PosAdorn<TyExpr>; right : PosAdorn<Expr> }
and InternalValConAccessRec = { valCon : PosAdorn<Expr>; typ : PosAdorn<TyExpr> }
and CallRec =         { func : PosAdorn<Expr>; args : PosAdorn<PosAdorn<Expr> list> }
and TemplateApplyExpRec = { func : PosAdorn<Expr>; templateArgs : PosAdorn<TemplateApply> }
and RecordExprRec =   { recordTy : PosAdorn<TyExpr>; templateArgs : PosAdorn<TemplateApply> option; initFields : PosAdorn<(PosAdorn<string> * PosAdorn<Expr>) list> }
and ArrayMakeExpRec = { typ : PosAdorn<TyExpr>; initializer : PosAdorn<Expr> }
and Expr = SequenceExp of PosAdorn<PosAdorn<Expr> list>
          | BinaryOpExp of BinaryOpRec
          | IfElseExp of IfElseRec
          | LetExp of LetRec
          | InternalDeclareVar of InternalDeclareVarExpRec // Only used internally for declaring variables
                                                           // that will actually be outputted by the compiler
          | InternalValConAccess of InternalValConAccessRec // Only used internally for type checking pattern
                                                            // matching. Essentially acts like a type cast
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
and BinaryOps = Add | Subtract | Multiply | Divide | Modulo | BitwiseOr | BitwiseAnd | LogicalOr | LogicalAnd | Equal | NotEqual | GreaterOrEqual | LessOrEqual | Greater | Less
and UnaryOps = LogicalNot | BitwiseNot

and VarMutationRec =    { varName : PosAdorn<string> }
and ArrayMutationRec =  { array : PosAdorn<LeftAssign>; index : PosAdorn<Expr> }
and RecordMutationRec = { record : PosAdorn<LeftAssign>; fieldName : PosAdorn<string> }
and LeftAssign = VarMutation of VarMutationRec
               | ArrayMutation of ArrayMutationRec
               | RecordMutation of RecordMutationRec

let unwrap<'a> ((_, _, c) : PosAdorn<'a>) = c
let getPos<'a> ((a, _, _) : PosAdorn<'a>) = a
let getType<'a> ((_, b, _) : PosAdorn<'a>) = b
let dummyPos : Position = {pos_fname=""
                           pos_lnum = -1
                           pos_bol = -1
                           pos_cnum = -1}
let dummyWrap<'a> c : PosAdorn<'a> = ((dummyPos, dummyPos), None, c)
let clean<'a> ((_, _, c) : PosAdorn<'a>) : PosAdorn<'a> = dummyWrap c
let cleanAll haystack = TreeTraversals.map1 (fun pos -> dummyPos) haystack

let wrapWithType<'a> t c : PosAdorn<'a> = ((dummyPos, dummyPos), Some t, c)

let templateToTemplateApply template =
    let tyExprs = template.tyVars |> unwrap |> List.map (ForallTy >> dummyWrap) |> dummyWrap
    let capExprs = template.capVars |> unwrap |> List.map (CapacityNameExpr >> dummyWrap) |> dummyWrap
    {tyExprs=tyExprs; capExprs=capExprs}