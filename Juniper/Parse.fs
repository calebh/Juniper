module Parse
open FParsec
open Ast
open FSharpx

let singleLineComment = skipString "//" >>. restOfLine true >>% ()
let multiLineComment = skipString "(*" >>. skipCharsTillString "*)" true System.Int32.MaxValue
let ws = spaces .>> (choice [singleLineComment; multiLineComment] >>. spaces |> many)

let pipe6 p1 p2 p3 p4 p5 p6 f = 
    pipe5 p1 p2 p3 p4 (FParsec.Primitives.tuple2 p5 p6)
          (fun x1 x2 x3 x4 (x5, x6) -> f x1 x2 x3 x4 x5 x6)

let stringLiteral containingChar asciiOnly =
    let str s = pstring s
    let normalCharSnippet = manySatisfy (fun c -> c <> '\\' && c <> containingChar && (not asciiOnly || (int) c < 256))
    let escapedChar = str "\\" >>. (anyOf "\\\"nrt" |>> function
                                                        | 'n' -> "\n"
                                                        | 'r' -> "\r"
                                                        | 't' -> "\t"
                                                        | c   -> string c)
    between (skipChar containingChar) (skipChar containingChar)
            (stringsSepBy normalCharSnippet escapedChar)

type LeftRecursiveExp = CallArgs of PosAdorn<PosAdorn<Expr> list>
                      | ArrayIndex of PosAdorn<Expr>
                      | TypeConstraintType of PosAdorn<TyExpr>
                      | FieldAccessName of PosAdorn<string>
                      | UnsafeTypeCastType of PosAdorn<TyExpr>

type LeftRecursiveTyp = ArrayTyCap of PosAdorn<TyExpr>
                      | RefTyRef of PosAdorn<unit>
                      | ApplyTyTemplate of PosAdorn<TemplateApply>

type LeftRecursiveLeftAssign = ArrayMutationIndex of PosAdorn<Expr>
                             | RecordMutationField of PosAdorn<string>

let (templateApply, templateApplyRef) = createParserForwardedToRef()
let (elifList, elifListRef) = createParserForwardedToRef()
let (pattern, patternRef) = createParserForwardedToRef()

let opp = new OperatorPrecedenceParser<PosAdorn<Expr>, Position, unit>()
let expr = attempt opp.ExpressionParser

let typOpp = new OperatorPrecedenceParser<PosAdorn<TyExpr>, Position, unit>()

let leftRecurse pterm pchain makeTree =
    pipe2
        pterm
        pchain
        (fun term chain ->
            List.fold
                (fun accumTerm ((_, rightPos), chainElem) ->
                    let ((leftPos, _), _) = accumTerm
                    ((leftPos, rightPos), makeTree accumTerm chainElem))
                term
                chain)

let adjustPosition offset (pos: Position) =
    Position(pos.StreamName, pos.Index + int64 offset,
             pos.Line, pos.Column + int64 offset)

// To simplify infix operator definitions, we define a helper function.
let addInfixOperator str prec assoc mapping (opp : OperatorPrecedenceParser<_, _, _>) =
    let op = InfixOperator(str, getPosition .>> ws, prec, assoc, (),
                           fun opPos leftTerm rightTerm ->
                               let ((posl, _), _) = leftTerm
                               let ((_, posr), _) = rightTerm
                               mapping
                                   (posl, posr)
                                   ((adjustPosition -str.Length opPos), opPos)
                                   leftTerm rightTerm)
    opp.AddOperator(op)

let addPrefixOperator str prec isAssoc mapping (opp : OperatorPrecedenceParser<_, _, _>) =
    let op = PrefixOperator(str, getPosition .>> ws, prec, isAssoc, (),
                               fun opPosR term ->
                                   let ((_, posr), _) = term
                                   let opPosL = (adjustPosition -str.Length opPosR)
                                   mapping
                                       (opPosL, posr)
                                       (opPosL, opPosR)
                                       term)
    opp.AddOperator(op)

let infix str precidence op assoc f opp =
    addInfixOperator str precidence assoc
        (fun overallPos opPos l r ->
            (overallPos, f l (opPos, op) r))
        opp

let prefix str precidence op f opp =
    addPrefixOperator str precidence true
        (fun overallPos opPos term ->
            (overallPos,  f (opPos, op) term))
        opp

List.iter
    (fun f -> f  (fun l op r -> BinaryOpExp {left=l; right=r; op=op}) opp)
    [infix "|>" 1 Pipe Associativity.Left;
    infix "or"  2 LogicalOr Associativity.Left;
    infix "and" 3 LogicalAnd Associativity.Left;
    infix "|||" 4 BitwiseOr Associativity.Left;
    infix "^^^" 5 BitwiseXor Associativity.Left;
    infix "&&&" 6 BitwiseAnd Associativity.Left;
    infix "=="  7 Equal Associativity.Left;
    infix "!="  7 NotEqual Associativity.Left;
    infix "<"   8 Less Associativity.None;
    infix ">"   8 Greater Associativity.None;
    infix "<="  8 LessOrEqual Associativity.None;
    infix ">="  8 GreaterOrEqual Associativity.None;
    infix ">>>" 9 BitshiftRight Associativity.Left;
    infix "<<<" 9 BitshiftLeft Associativity.Left;
    infix "+"   10 Add Associativity.Left;
    infix "-"   10 Subtract Associativity.Left;
    infix "*"   11 Multiply Associativity.Left;
    infix "/"   11 Divide Associativity.Left;
    infix "mod" 11 Modulo Associativity.Left]

List.iter
    (fun f -> f (fun op term -> UnaryOpExp {op=op; exp=term}) opp)
    [prefix "-"  12 Negate;
    prefix "~~~" 12 BitwiseNot;
    prefix "not " 12 LogicalNot;
    prefix "!" 12 Deref]

infix "*" 1 () Associativity.Left
    (fun l _ r ->
        let (_, left) = l
        let (_, right) = r
        match (left, right) with
        | (TupleTy lstL, TupleTy lstR) -> TupleTy (List.append lstL lstR)
        | (TupleTy lstL, _)            -> TupleTy (List.append lstL [r])
        | (_, TupleTy lstR)            -> TupleTy (l::lstR)
        | _                            -> TupleTy [l; r]) typOpp

let pos p : Parser<PosAdorn<'a>, 'b> = getPosition .>>. p .>>. getPosition |>> fun ((pos1, value), pos2) -> ((pos1, pos2), value)

let betweenChar left p right = skipChar left >>. ws >>. p .>> ws .>> skipChar right

let idn : Parser<string, unit> =
    let inRange (c : char) (low, high) =
        let i = int c
        low <= i && i <= high
    
    let isValidCodePoint c = List.exists (inRange c)

    let isAsciiIdStart c    = isAsciiLetter c || c = '_'
    let isAsciiIdContinue c = isAsciiIdStart c || isDigit c
    
    // See https://msdn.microsoft.com/en-us/library/565w213d.aspx
    let preCheckStart c    = isAsciiLetter c || c = '_' || isValidCodePoint c
                                [(0x00A8, 0x00A8); (0x00AA, 0x00AA); (0x00AD, 0x00AD);
                                 (0x00AF, 0x00AF); (0x00B2, 0x00B5); (0x00B7, 0x00BA);
                                 (0x00BC, 0x00BE); (0x00C0, 0x00D6); (0x00D8, 0x00F6);
                                 (0x00F8, 0x00FF); (0x0100, 0x02FF); (0x0370, 0x167F);
                                 (0x1681, 0x180D); (0x180F, 0x1DBF); (0x1E00, 0x1FFF);
                                 (0x200B, 0x200D); (0x202A, 0x202E); (0x203F, 0x2040);
                                 (0x2054, 0x2054); (0x2060, 0x206F); (0x2070, 0x20CF);
                                 (0x2100, 0x218F); (0x2460, 0x24FF); (0x2776, 0x2793);
                                 (0x2C00, 0x2DFF); (0x2E80, 0x2FFF); (0x3004, 0x3007);
                                 (0x3021, 0x302F); (0x3031, 0x303F); (0x3040, 0xD7FF);
                                 (0xF900, 0xFD3D); (0xFD40, 0xFDCF); (0xFDF0, 0xFE1F);
                                 (0xFE30, 0xFE44); (0xFE47, 0xFFFD); (0x10000, 0x1FFFD);
                                 (0x20000, 0x2FFFD); (0x30000, 0x3FFFD); (0x40000, 0x4FFFD);
                                 (0x50000, 0x5FFFD); (0x60000, 0x6FFFD); (0x70000, 0x7FFFD);
                                 (0x80000, 0x8FFFD); (0x90000, 0x9FFFD); (0xA0000, 0xAFFFD);
                                 (0xB0000, 0xBFFFD); (0xC0000, 0xCFFFD); (0xD0000, 0xDFFFD);
                                 (0xE0000, 0xEFFFD)]
    let preCheckContinue c = preCheckStart c || isDigit c || isValidCodePoint c
                                [(0x0300, 0x036F); (0x1DC0, 0x1DFF); (0x20D0, 0x20FF); (0xFE20, 0xFE2F)]

    let opts =
        IdentifierOptions(
            isAsciiIdStart = isAsciiIdStart,
            isAsciiIdContinue = isAsciiIdContinue,
            preCheckStart = preCheckStart,
            preCheckContinue = preCheckContinue,
            // See http://www.unicode.org/reports/tr15/#Introduction
            normalization = System.Text.NormalizationForm.FormC,
            normalizeBeforeValidation = true
        )
    identifier opts

let separatedList p c = sepBy p (ws >>. skipChar c >>. ws)
let separatedList1 p c = sepBy1 p (ws >>. skipChar c >>. ws)

let moduleQualifier =
    pipe2
        (pos idn .>> skipChar ':')
        (pos idn .>> ws)
        (fun moduleName decName -> {module_=moduleName; name=decName})

let templateDec =
    (skipChar '<' >>. ws >>. (separatedList (skipChar '\'' >>. pos idn) ',' |> pos)) |>>
    (fun tyVars -> {tyVars = tyVars})

let tyExpr = attempt typOpp.ExpressionParser

// leftRecursiveTyp
let leftRecursiveTyp =
    let openBracket = skipChar '[' >>. ws
    let closingBracket = ws >>. skipChar ']' >>. ws
    let arrayTyCap = between openBracket closingBracket tyExpr |>> ArrayTyCap
    let refTyRef = pstring "ref" >>. ws >>% () |> pos |>> RefTyRef
    let applyTyTemplate = templateApply .>> ws |>> ApplyTyTemplate
    (choice [arrayTyCap; refTyRef; applyTyTemplate]) |> pos |> many

// tyExpr
do
    let varTy =
        skipChar '\'' >>. idn |> pos |>> VarTy
    let name =
        pos idn |>>
        (fun (p, n) ->
            match n with
            | "uint8" -> BaseTy (p, TyUint8)
            | "uint16" -> BaseTy (p, TyUint16)
            | "uint32" -> BaseTy (p, TyUint32)
            | "uint64" -> BaseTy (p, TyUint64)
            | "int8" -> BaseTy (p, TyInt8)
            | "int16" -> BaseTy (p, TyInt16)
            | "int32" -> BaseTy (p, TyInt32)
            | "int64" -> BaseTy (p, TyInt64)
            | "bool" -> BaseTy (p, TyBool)
            | "unit" -> BaseTy (p, TyUnit)
            | "float" -> BaseTy (p, TyFloat)
            | "double" -> BaseTy (p, TyDouble)
            | "pointer" -> BaseTy (p, TyPointer)
            | "string" -> BaseTy (p, TyString)
            | _ -> NameTy (p, n))
    let mQual = moduleQualifier |>> ModuleQualifierTy
    let fn =
        pipe2
            (skipChar '(' >>. separatedList (ws >>. tyExpr .>> ws) ',' .>> skipChar ')' .>> ws .>> skipString "->" .>> ws)
            tyExpr
            (fun argTys retTy -> FunTy {template = None; args = argTys; returnType = retTy})
    let parens = skipChar '(' >>. ws >>. tyExpr .>> ws .>> skipChar ')' |>> ParensTy
    let natNum = pint64 |> pos |>> NatNumTy
    let t = choice (List.map attempt [natNum; mQual; varTy; name; fn; parens]) |> pos .>> ws
    typOpp.TermParser <-
        leftRecurse
            t
            leftRecursiveTyp
            (fun term chainElem ->
                match chainElem with
                | ArrayTyCap cap -> ArrayTy {valueType=term; capacity=cap}
                | RefTyRef _ -> RefTy term
                | ApplyTyTemplate template -> ApplyTy {tyConstructor=term; args=template})

// Pattern
do
    let varPattern =
        pipe3
            (pstring "mutable" |> opt |>> Option.isSome |> pos .>> ws)
            (pos idn .>> ws)
            (skipChar ':' >>. ws >>. tyExpr |> opt .>> ws)
            (fun mut name typ ->
                MatchVar {varName=name; mutable_=mut; typ=typ}) |> pos
    let intPattern = pint64 |> pos |>> MatchIntVal |> pos
    let floatPattern = pfloat |> pos |>> MatchFloatVal |> pos
    let truePattern = skipString "true" |> pos |>> MatchTrue |> pos
    let falsePattern = skipString "false" |> pos |>> MatchFalse |> pos
    let valConEnd = opt templateApply .>> ws .>>. (skipChar '(' >>. ws >>. (opt pattern) .>> ws .>> skipChar ')') .>> ws
    let valConPattern =
        pipe2
            (pos idn .>> ws)
            valConEnd
            (fun (posn, name) (template, innerPattern) ->
                MatchValCon {name=(posn, Choice1Of2 name); template=template; innerPattern=innerPattern}) |> pos
    let valConModQualPattern =
        pipe2
            (pos moduleQualifier .>> ws)
            valConEnd
            (fun (posm, modQual) (template, innerPattern) ->
                MatchValCon {name=(posm, Choice2Of2 modQual); template=template; innerPattern=innerPattern}) |> pos
    let underscorePattern = skipChar '_' |> pos |>> MatchUnderscore |> pos
    let recordPatternEnd = opt templateApply .>> ws .>>. (skipChar '{' >>. ws >>. (separatedList (pos idn .>>. (ws >>. skipChar '=' >>. pattern .>> ws)) ';' |> pos .>> ws .>> skipChar '}' .>> ws))
    let recordPattern =
        pipe2
            (pos idn .>> ws)
            recordPatternEnd
            (fun (posn, name) (template, fields) ->
                MatchRecCon {name=(posn, Choice1Of2 name); template=template; fields=fields}) |> pos
    let recordModQualPattern =
        pipe2
            (pos moduleQualifier .>> ws)
            recordPatternEnd
            (fun (posn, modQual) (template, fields) ->
                MatchRecCon {name=(posn, Choice2Of2 modQual); template=template; fields=fields}) |> pos
    let unitPattern = skipString "()" |> pos |>> MatchUnit |> pos
    let parensPattern = betweenChar '(' pattern ')'
    let tuplePattern = betweenChar '(' (separatedList pattern ',') ')' |> pos |>> MatchTuple |> pos
    patternRef := choice (List.map attempt [intPattern; floatPattern; truePattern;
                          falsePattern; valConPattern; valConModQualPattern;
                          underscorePattern; recordPattern; recordModQualPattern; unitPattern;
                          parensPattern; tuplePattern; varPattern])

// leftRecursiveLeftAssign
let leftRecursiveLeftAssign =
    let arrayMutationIndex = betweenChar '[' expr ']' |>> ArrayMutationIndex
    let recordMutationField = skipChar '.' >>. pos idn |>> RecordMutationField
    choice [arrayMutationIndex; recordMutationField] |> pos .>> ws |> many

let leftAssign =
    let varMutation = idn |> pos |>> VarMutation
    let modQualifierMutation = moduleQualifier |> pos |>> ModQualifierMutation
    let term = (varMutation <|> modQualifierMutation) |> pos .>> ws
    leftRecurse
        term
        leftRecursiveLeftAssign
        (fun term chainElem ->
            match chainElem with
            | ArrayMutationIndex index -> ArrayMutation {array=term; index=index}
            | RecordMutationField fname -> RecordMutation {record=term; fieldName=fname})

let functionReturnType = skipChar ':' >>. ws >>. tyExpr .>> ws

let functionClause delimiter =
    let functionArguments =
        betweenChar '(' (separatedList (pos idn .>>. opt (ws >>. skipChar ':' >>. ws >>. tyExpr)) ',' |> pos) ')' .>> ws
    let body = expr
    pipe3
        functionArguments ((opt functionReturnType) .>> skipString delimiter .>> ws) body
        (fun a r b -> {returnType = r; arguments = a; body = b})

// leftRecursiveExp
let leftRecursiveExp =
    let callArgs = betweenChar '(' (separatedList expr ',' |> pos) ')' |>> CallArgs
    let arrayIndex = betweenChar '[' expr ']' |>> ArrayIndex
    let typeConstraint = skipChar ':' >>. ws >>. tyExpr |>> TypeConstraintType
    let fieldAccessName = skipChar '.' >>. ws >>. attempt idn |> pos |>> FieldAccessName
    let unsafeTypeCast = skipString "::::" >>. ws >>. tyExpr |>> UnsafeTypeCastType
    List.map attempt [callArgs; arrayIndex; unsafeTypeCast; typeConstraint; fieldAccessName] |> choice |> pos .>> ws |> many

// elifList
do
    let elseEnd = pstring "else" >>. ws >>. expr .>> ws .>> pstring "end"
    let pelif =
        pipe3
            (pstring "elif" >>. ws >>. expr .>> ws)
            (pstring "then" >>. ws >>. expr .>> ws)
            elifList
            (fun condition trueBranch falseBranch ->
                IfElseExp {
                    condition=condition;
                    trueBranch=trueBranch;
                    falseBranch=falseBranch
                }) |> pos
    elifListRef := choice [elseEnd; pelif]

// expr
do
    let punit = skipString "()" >>% () |> pos |>> UnitExp
    let parens = betweenChar '(' (expr |>> unwrap) ')'
    let ptrue = skipString "true" |> pos |>> TrueExp
    let pfalse = skipString "false" |> pos |>> FalseExp
    let pint = pos pint64 |>> IntExp .>> notFollowedByString "."
    let pdouble = pos pfloat |>> DoubleExp
    let pfloat = pos (pfloat .>> skipChar 'f') |>> FloatExp
    let pint8 = pos (pint64 .>> skipString "i8") |>> Int8Exp
    let pint16 = pos (pint64 .>> skipString "i16") |>> Int16Exp
    let pint32 = pos (pint64 .>> skipString "i32") |>> Int32Exp
    let pint64' = pos (pint64 .>> skipString "i64") |>> Int64Exp
    let puint8 = pos (pint64 .>> skipString "u8") |>> UInt8Exp
    let puint16 = pos (pint64 .>> skipString "u16") |>> UInt16Exp
    let puint32 = pos (pint64 .>> skipString "u32") |>> UInt32Exp
    let puint64 = pos (pint64 .>> skipString "u64") |>> UInt64Exp
    let charlist = pos (stringLiteral '\'' true) |>> CharListLiteral
    let str = pos (stringLiteral '"' true) |>> StringLiteral
    let seq = betweenChar '(' (separatedList (attempt expr) ';' |> pos) ')' |>> SequenceExp
    let quit = skipString "quit" >>. ws >>. opt (skipChar '<' >>. ws >>. tyExpr .>> ws .>> skipChar '>') .>> ws .>> skipChar '(' .>> ws .>> skipChar ')' |>> QuitExp
    let applyTemplateToFunc =
        pipe2
            (pos ((attempt moduleQualifier |>> Choice2Of2) <|> (idn |>> Choice1Of2)) .>> ws)
            templateApply
            (fun funExpr temp -> TemplateApplyExp {func = funExpr; templateArgs = temp})
    let pIf =
        pipe3
            (skipString "if" >>. ws >>. expr .>> ws)
            (skipString "then" >>. ws >>. expr .>> ws)
            elifList
            (fun condition trueBranch falseBranch ->
                IfElseExp {
                    condition = condition;
                    trueBranch = trueBranch;
                    falseBranch = falseBranch
                })
    let pLet =
        pipe2
            (pstring "let" >>. ws >>. pattern .>> ws .>> skipChar '=' .>> ws)
            (expr .>> ws)
            (fun pat expr ->
                LetExp {left=pat; right=expr})
    let assign =
        pipe3
            (skipString "set" >>. ws >>. (skipString "ref" |> opt |>> Option.isSome |> pos) .>> ws)
            (leftAssign .>> ws .>> skipChar '=' .>> ws)
            expr
            (fun ref_ left right -> AssignExp {left=left; right=right; ref=ref_})
    let forLoop =
        pipe6
            (pstring "for" >>. ws >>. pos idn .>> ws)
            (skipChar ':' >>. ws >>. tyExpr .>> ws |> opt)
            (pstring "in" >>. ws >>. expr .>> ws)
            ((pstring "to" >>% Upto) <|> (pstring "downto" >>% Downto) |> pos .>> ws)
            expr
            (pstring "do" >>. ws >>. expr .>> pstring "end")
            (fun varName typ start direction end_ body ->
                ForLoopExp {varName=varName; typ=typ; start=start; direction=direction; end_=end_; body=body})
    let doWhileLoop =
        pipe2
            (pstring "do" >>. ws >>. expr .>> ws)
            (pstring "while" >>. ws >>. expr .>> ws .>> pstring "end")
            (fun body condition -> DoWhileLoopExp {body=body; condition=condition})
    let whileLoop =
        pipe2
            (pstring "while" >>. ws >>. expr .>> ws .>> pstring "do" .>> ws)
            (expr .>> ws .>> pstring "end")
            (fun condition body -> WhileLoopExp {condition=condition; body=body})
    let fn = skipString "fn" >>. ws >>. functionClause "->" .>> ws .>> skipString "end" |> pos |>> LambdaExp
    let case =
        let caseClause = (pattern .>> ws) .>>. (pstring "=>" >>. ws >>. expr)
        pipe2
            (pstring "case" >>. ws >>. expr .>> pstring "of" .>> ws)
            ((skipChar '|' >>. ws >>. caseClause) |> many1 |> pos .>> ws .>> pstring "end")
            (fun on clauses ->
                CaseExp {on=on; clauses=clauses})
    let recordExpr =
        let fieldList = separatedList ((pos idn .>> ws) .>>. (skipChar '=' >>. ws >>. expr)) ';'
        pipe3
            (pos ((attempt moduleQualifier |>> Choice2Of2) <|> (idn |>> Choice1Of2)) .>> ws)
            (templateApply |> opt .>> ws)
            (betweenChar '{' (ws >>. fieldList .>> ws) '}' |> pos)
            (fun recordTy template fields ->
                RecordExp {recordTy=recordTy; templateArgs=template; initFields=fields})
    let arrayLiteral = betweenChar '[' (separatedList expr ',') ']' |> pos |>> ArrayLitExp
    let pref = pstring "ref" >>. ws >>. expr |>> RefExp
    let modQual = moduleQualifier |> pos |>> ModQualifierExp
    let varReference = attempt idn |> pos |>> VarExp
    let arrayMake =
        pipe2
            (skipString "array" >>. ws >>. tyExpr .>> ws)
            ((skipString "of" >>. ws >>. expr |> opt) .>> ws .>> skipString "end")
            (fun arrTy initializer -> ArrayMakeExp {typ=arrTy; initializer=initializer})
    let inlineCpp =
        let normalCharSnippet = manySatisfy (fun c -> c <> '\\' && c <> '#')
        let escapedChar = pstring "\\" >>. (anyOf "\\#" |>> string)
        between (pstring "#") (pstring "#") (stringsSepBy normalCharSnippet escapedChar) |> pos |>> InlineCode
    let tuple = betweenChar '(' (separatedList1 expr ',') ')' |>> TupleExp
    let smartpointer = (skipString "smartpointer" >>. ws >>. (pos idn) .>> ws) .>>. (skipString "in" >>. ws >>. expr .>> ws .>> skipString "end") |>> Smartpointer
    let e = choice (List.map attempt [punit; parens; ptrue; pfalse; charlist; str;
                    pint8; pint16; pint32; pint64'; puint8; puint16; puint32; puint64;
                    pint; pfloat; pdouble; smartpointer;
                    fn; quit; tuple; recordExpr; applyTemplateToFunc; seq;
                    modQual; forLoop; doWhileLoop; whileLoop;
                    pLet; pIf; assign; case;
                    arrayLiteral; pref;
                    arrayMake; inlineCpp; varReference]) .>> ws |> pos
    opp.TermParser <-
        leftRecurse
            e
            leftRecursiveExp
            (fun term chainElem ->
                match chainElem with
                | CallArgs args -> CallExp {func=term; args=args}
                | ArrayIndex index -> ArrayAccessExp {array=term; index=index}
                | TypeConstraintType typ -> TypeConstraint {exp=term; typ=typ}
                | FieldAccessName fieldName -> RecordAccessExp {record=term; fieldName=fieldName}
                | UnsafeTypeCastType typ -> UnsafeTypeCast {exp=term; typ=typ}) |> attempt

// templateApply
do
    templateApplyRef :=
        (skipChar '<' >>. ws >>. separatedList tyExpr ',' .>> ws .>> skipChar '>') |> pos |>>
        (fun tyExprs -> {tyExprs = tyExprs}) |> pos

// Typeclass predicates
let typeclassPred =
    pipe2
        (idn |> pos)
        templateApply
        (fun name application -> {name = name; templateApply = application})

let typeclassPreds =
    separatedList (pos typeclassPred) ','

let typeclassWherePreds =
    skipString "where" >>. ws >>. typeclassPreds

let funName = skipString "fun" >>. ws >>. pos idn .>> ws

let functionArguments =
    betweenChar '(' (separatedList (pos idn .>>. opt (ws >>. skipChar ':' >>. ws >>. tyExpr)) ',' |> pos) ')' .>> ws

let functionp =
    let body = expr
    pipe6
        funName
        (templateDec |> pos |> opt)
        functionArguments
        (opt functionReturnType)
        ((typeclassWherePreds |> pos |> opt) .>> skipString "=" .>> ws)
        body
        (fun name template arguments returnType predicates body ->
            let (clausePosL, _) = getPos arguments
            let (_, clausePosR) = getPos arguments
            let clausePos = (clausePosL, clausePosR)
            let clause = (clausePos, { returnType = returnType; arguments = arguments; body = body })
            { name=name; template=template; predicates=predicates; clause=clause })

let functionDec = functionp |>> FunctionDec

let moduleName = skipString "module" >>. ws >>. pos idn .>> ws |>> ModuleNameDec

let recordDec =
    pipe3
        (skipString "type" >>. ws >>. pos idn .>> ws)
        (templateDec |> pos |> opt .>> ws .>> skipChar '=' .>> ws .>> skipChar '{' .>> ws)
        (separatedList ((pos idn .>> ws .>> skipChar ':' .>> ws) .>>. tyExpr) ';' |> pos .>> ws .>> skipChar '}' .>> ws)
        (fun name template fields ->
            RecordDec {name=name; template=template; fields=fields})

let unionDec =
    let valueConstructor = pos idn .>> ws .>>. (skipString "of" >>. ws >>. tyExpr |> opt .>> ws)
    pipe3
        (skipString "type" >>. ws >>. pos idn .>> ws)
        (templateDec |> pos |> opt .>> ws .>> skipChar '=' .>> ws)
        (separatedList valueConstructor '|' |> pos)
        (fun name template valCons ->
            UnionDec {name=name; template=template; valCons=valCons})

let letDec =
    pipe3
        (skipString "let" >>. ws >>. pos idn .>> ws)
        (skipChar ':' >>. ws >>. tyExpr |> opt .>> ws)
        (skipChar '=' >>. ws >>. expr .>> ws)
        (fun name typ right ->
            LetDec {varName=name; typ=typ; right=right})

let openDec = skipString "open" >>. ws >>. skipChar '(' >>. ws >>. (separatedList (pos idn) ',' |> pos) .>>
                ws .>> skipChar ')' .>> ws |>> OpenDec

let includeDec = skipString "include" >>. ws >>. skipChar '(' >>. ws >>. separatedList (pos (stringLiteral '"' false)) ',' |> pos .>>
                    ws .>> skipChar ')' .>> ws |>> IncludeDec

let typeclassDec =
    let functionArguments =
        betweenChar '(' (separatedList (pos idn .>>. (ws >>. skipChar ':' >>. ws >>. tyExpr)) ',' |> pos) ')' .>> ws

    let typeClassDecFun =
        pipe5
            funName
            (templateDec |> pos |> opt)
            functionArguments
            functionReturnType
            (pos typeclassWherePreds |> opt)
            (fun name template arguments returnType preds ->
                {name = name; template = template; arguments = arguments; returnType = returnType;
                 predicates = preds})
    
    pipe4
        (skipString "typeclass" >>. ws >>. (pos idn) .>> ws)
        (templateDec)
        (typeclassWherePreds |> pos |> opt)
        ((many (typeClassDecFun |> pos) |> pos) .>> (skipString "end"))
        (fun name template predicates funs ->
            {name = name; template = template; predicates = predicates; functions = funs}) |>
    pos |>>
    Typeclass

let typeclassInstanceDec =
    pipe3
        (skipString "instance" >>. ws >>. (pos typeclassPred) .>> ws)
        (typeclassWherePreds |> pos |> opt)
        (pos (many (pos functionp)) .>> ws .>> skipString "end")
        (fun instanceOf predicates funcs ->
            {instanceOf = instanceOf; predicates = predicates; functions = funcs})

let program =
    let declarationTypes = [functionDec; moduleName; attempt recordDec; unionDec;
                            letDec; openDec; includeDec; typeclassDec]
    ws >>. many (choice declarationTypes |> pos .>> ws) .>> eof