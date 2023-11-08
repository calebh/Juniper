module Parse
open FParsec
open Ast
open Error
open Extensions

let fatalizeAnyError (p : Parser<'a, 'u>) : Parser<'a, 'u> =
    fun stream ->
        let reply = p stream
        if reply.Status = Ok then
            reply
        else
            Reply(FatalError, reply.Error)

let singleLineComment = skipString "//" >>. restOfLine true >>% () <?> "Single line comment"
let multiLineComment = skipString "/*" >>. skipCharsTillString "*/" true System.Int32.MaxValue <?> "Multiline comment"
let ws = spaces .>> ((choice [singleLineComment; multiLineComment] >>. spaces) |> many) <?> "Whitespace or comment"
let ws1 = (spaces1 <|> singleLineComment <|> multiLineComment) .>> spaces .>> (choice [singleLineComment; multiLineComment] >>. spaces |> many) <?> "Whitespace or comment (1 or more)"
let wsNoNewline = 
    let nonNewlineWsP = anyOf [' '; '\t'] |> many
    nonNewlineWsP .>> ((choice [singleLineComment; multiLineComment] >>. nonNewlineWsP) |> many) <?> "Non-newline whitespace or comment"

//let wsNewline = wsNoNewline .>> (choice [skipChar '\n'; skipChar '\r']) .>> ws

let pipe2' p1 p2 f =
    p1 .>>.? p2 |>> (fun (a, b) -> f a b)

let pipe3' p1 p2 p3 f =
    p1 .>>.? p2 .>>.? p3 |>> (fun ((a, b), c) -> f a b c)

let pipe4' p1 p2 p3 p4 f = 
    p1 .>>.? p2 .>>.? p3 .>>.? p4 |>>
    (fun (((x1, x2), x3), x4) -> f x1 x2 x3 x4)

let pipe5' p1 p2 p3 p4 p5 f = 
    p1 .>>.? p2 .>>.? p3 .>>.? p4 .>>.? p5 |>>
    (fun ((((x1, x2), x3), x4), x5) -> f x1 x2 x3 x4 x5)

let pipe6' p1 p2 p3 p4 p5 p6 f = 
    p1 .>>.? p2 .>>.? p3 .>>.? p4 .>>.? p5 .>>.? p6 |>>
    (fun (((((x1, x2), x3), x4), x5), x6) -> f x1 x2 x3 x4 x5 x6)

let pipe6 p1 p2 p3 p4 p5 p6 f = 
    pipe5 p1 p2 p3 p4 (tuple2 p5 p6)
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

type LeftRecursiveExp = CallArgs of PosAdorn<CallArg list>
                      | ArrayIndex of PosAdorn<Expr>
                      | TypeConstraintType of PosAdorn<TyExpr>
                      | FieldAccessName of PosAdorn<string>
                      | RefFieldAccessName of PosAdorn<string>

type LeftRecursiveTyp = ArrayTyCap of PosAdorn<TyExpr>
                      | RefTyRef of PosAdorn<unit>
                      | ApplyTyTemplate of PosAdorn<TemplateApply>

let (templateApply, templateApplyRef) = createParserForwardedToRef()
let (pattern, patternRef) = createParserForwardedToRef()

let opp = new OperatorPrecedenceParser<PosAdorn<Expr>, Position, unit>()
let expr = opp.ExpressionParser

let exprws = expr .>> ws

let tyExprOpp = new OperatorPrecedenceParser<PosAdorn<TyExpr>, Position, unit>()
let tyExpr = tyExprOpp.ExpressionParser

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
    (fun f -> f (fun l op r -> AssignExp { left = ConvertAst.convertToLHS "The left hand side of the assignment operation contained an invalid expression." l; op=op; right=r}) opp)
    [infix "=" 1 Assign Associativity.Right;
    infix "+=" 1 AddAssign Associativity.Right;
    infix "-=" 1 SubAssign Associativity.Right;
    infix "*=" 1 MulAssign Associativity.Right;
    infix "/=" 1 DivAssign Associativity.Right;
    infix "%=" 1 ModAssign Associativity.Right;
    infix "&=" 1 BitwiseAndAssign Associativity.Right;
    infix "|=" 1 BitwiseOrAssign Associativity.Right;
    infix "^=" 1 BitwiseXorAssign Associativity.Right;
    infix "<<=" 1 BitwiseLShiftAssign Associativity.Right;
    infix ">>=" 1 BitwiseRShiftAssign Associativity.Right;]

List.iter
    // f here is the partially applied infix function
    (fun f -> f (fun l op r -> BinaryOpExp {left=l; right=r; op=op}) opp)
    [infix "|>" 2 Pipe Associativity.Left;
    infix "||"  3 LogicalOr Associativity.Left;
    infix "&&" 4 LogicalAnd Associativity.Left;
    infix "|" 5 BitwiseOr Associativity.Left;
    infix "^" 6 BitwiseXor Associativity.Left;
    infix "&" 7 BitwiseAnd Associativity.Left;
    infix "=="  8 Equal Associativity.Left;
    infix "!="  8 NotEqual Associativity.Left;
    infix "<"   9 Less Associativity.None;
    infix ">"   9 Greater Associativity.None;
    infix "<="  9 LessOrEqual Associativity.None;
    infix ">="  9 GreaterOrEqual Associativity.None;
    infix ">>" 10 BitshiftRight Associativity.Left;
    infix "<<" 10 BitshiftLeft Associativity.Left;
    infix "+"   11 Add Associativity.Left;
    infix "-"   11 Subtract Associativity.Left;
    infix "*"   12 Multiply Associativity.Left;
    infix "/"   12 Divide Associativity.Left;
    infix "%"   12 Modulo Associativity.Left]

List.iter
    // f here is the partially applied prefix function
    (fun f -> f (fun op term -> UnaryOpExp {op=op; exp=term}) opp)
    [prefix "-"  13 Negate;
    prefix "~" 13 BitwiseNot;
    prefix "!" 13 LogicalNot;
    prefix "*" 13 Deref]

List.iter
    (fun f -> f (fun l op r -> CapacityOp {left=l; op=op; right=r}) tyExprOpp)
    [infix "+" 11 CapAdd Associativity.Left;
    infix "-"  11 CapSubtract Associativity.Left;
    infix "*"  12 CapMultiply Associativity.Left;
    infix "/"  12 CapDivide Associativity.Left]

List.iter
    (fun f -> f (fun op term -> CapacityUnaryOp {op=op; term=term}) tyExprOpp)
    [prefix "-" 12 CapNegate]

let pos p : Parser<PosAdorn<'a>, 'b> = getPosition .>>. p .>>. getPosition |>> fun ((pos1, value), pos2) -> ((pos1, pos2), value)

let betweenChar left p right = skipChar left >>. ws >>. p .>> ws .>> skipChar right

let id : Parser<string, unit> =
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
        (pos id .>> skipChar ':')
        (pos id .>> ws)
        (fun moduleName decName -> {module_=moduleName; name=decName})

let templateDec =
    let pCapVar =
        pipe2'
            ((pos id) .>> ws .>> skipChar ':' .>> ws)
            (pos (skipString "int"))
            (fun name kind ->
                (name, IntKind kind))
    let pTyVar =
        pipe2'
            (pos id)
            (pos ((ws >>. skipChar ':' >>. ws >>. skipChar '*') |> opt))
            (fun name (kindpos, _) ->
                (name, StarKind (kindpos, ())))
    let pTemplateVar = (attempt pCapVar) <|> pTyVar
    skipChar '<' >>. ws >>. ((separatedList1 pTemplateVar ',') |> pos) .>> ws .>> skipChar '>'

let record =
    pipe2
        ((skipString "packed" |> pos |> opt) .>> ws .>> skipChar '{' .>> ws)
        (separatedList ((pos id .>> ws .>> skipChar ':' .>> ws) .>>. tyExpr) ',' |> pos .>> ws .>> skipChar '}' .>> ws)
        (fun packed fields -> { packed=packed; fields=fields })

// leftRecursiveTyp
let leftRecursiveTyp =
    let openBracket = skipChar '[' >>. wsNoNewline
    let closingBracket = ws >>. skipChar ']' >>. wsNoNewline
    let arrayTyCap = between openBracket closingBracket tyExpr |>> ArrayTyCap
    let refTyRef = pstring "ref" >>. wsNoNewline >>% () |> pos |>> RefTyRef
    let applyTyTemplate = templateApply .>> wsNoNewline |>> ApplyTyTemplate
    ((choice [arrayTyCap; refTyRef; applyTyTemplate]) |> pos |> many) <?> "Type expression chain (array, ref or template appliction)"

// tyExpr
do
    let name =
        pos id |>>
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
            | "rcptr" -> BaseTy (p, TyPointer)
            | "string" -> BaseTy (p, TyString)
            | "ptr" -> BaseTy (p, TyRawPointer)
            | _ -> NameTy (p, n))
    let underscore = skipChar '_' |> pos |>> UnderscoreTy
    let mQual = moduleQualifier |>> ModuleQualifierTy
    let closureTy = betweenChar '|' (separatedList ((pos id .>> ws .>> skipChar ':' .>> ws) .>>. tyExpr) ',') '|' |> pos |>> ClosureTy
    let (fn1, fn2) =
        let closurep = betweenChar '(' (choice [attempt underscore; name; closureTy]) ')' |> pos
        let argsp = skipChar '(' >>. separatedList (ws >>. tyExpr .>> ws) ',' .>> skipChar ')' .>> ws .>> skipString "->" .>> ws
        let fn1 =
            pipe3
                closurep
                argsp
                tyExpr
                (fun closure argTys retTy ->
                    FunTy { closure=closure; args = argTys; returnType = retTy})
        let fn2 =
            (* If the user does not enter a closure type for this function signature,
                   assume the user intended the closure to be a type wildcard. *)
            ((argsp .>>. tyExpr) |> pos |>>
            (fun (post, (argTys, retTy)) ->
                // No closure was explicitly given. Desugar into a wildcard (underscore)
                let closure = (post, UnderscoreTy (post, ()))
                FunTy { closure=closure; args=argTys; returnType = retTy}))
        (fn1 <?> "Function type with no closure", fn2 <?> "Function type with closure")
    let tuple =
        pipe2
            (skipChar '(' >>. ws >>. tyExpr .>> ws .>> skipChar ',' .>> ws)
            ((separatedList1 tyExpr ',') .>> ws .>> skipChar ')')
            (fun tyHead tyRest ->
                TupleTy (tyHead::tyRest)) <?> "Tuple type"
    let recordTy = record |> pos |>> RecordTy <?> "Record type"
    let capConst = pos pint64 |>> CapacityConst <?> "Capacity constant"
    let inoutTy = (attempt (skipString "inout" .>> ws1)) >>. (fatalizeAnyError tyExpr) |>> InOutTy <?> "inout type"
    let t = choice ([capConst; inoutTy; attempt mQual; closureTy; attempt recordTy; attempt underscore; name; attempt fn1; attempt fn2; tuple]) |> pos .>> wsNoNewline
    tyExprOpp.TermParser <-
        (leftRecurse
            (t <?> "Type expression")
            leftRecursiveTyp
            (fun term chainElem ->
                match chainElem with
                | ArrayTyCap cap -> ArrayTy {valueType=term; capacity=cap}
                | RefTyRef _ -> RefTy term
                | ApplyTyTemplate template -> ApplyTy {tyConstructor=term; args=template})) <?> "Type expression"

let floatParser =
    fun stream ->
        let reply = numberLiteralE NumberLiteralOptions.DefaultFloat (expected "floating-point number") stream
        if reply.Status = Ok then
            let result = reply.Result
            if result.IsInteger then
                stream.Skip(-result.String.Length)
                Reply(Error, expected "floating-point number with decimal")
            else
                try
                    if result.IsDecimal then
                        Reply(result.String)
                    elif result.IsHexadecimal then
                        // TODO: Once there is widespread support for C++17
                        // hexadecimal floating literals, we can change this to result.String
                        // instead of converting to decimal
                        Reply((floatOfHexString result.String).ToString())
                    elif result.IsInfinity then
                        if result.HasMinusSign then
                            Reply(FatalError, messageError "The floating-point number is negative infinity.")
                        else
                            Reply(FatalError, messageError "The floating-point number is infinity.")
                    else
                        Reply(FatalError, messageError "The floating-point number is NaN.")
                with 
                | :? System.OverflowException ->
                    Reply(FatalError, messageError "Parsing the number resulted in an overflow.")
                | :? System.FormatException ->
                    stream.Skip(-result.String.Length)
                    Reply(FatalError, messageError "The floating-point number has an invalid format (this error is unexpected, please report this error message to fparsec@quanttec.com).")
        else
            Reply(reply.Status, reply.Error)

// Pattern
do
    let varPattern =
        pipe3
            (pstring "mut" |> opt |>> Option.isSome |> pos .>> ws)
            (pos id .>> ws)
            (skipChar ':' >>. ws >>. tyExpr |> opt .>> ws)
            (fun mut name typ ->
                MatchVar {varName=name; mutable_=mut; typ=typ}) |> pos
    let intPattern = pint64 |> pos |>> MatchIntVal |> pos
    let floatPattern = floatParser |> pos |>> MatchFloatVal |> pos
    let truePattern = skipString "true" |> pos |>> MatchTrue |> pos
    let falsePattern = skipString "false" |> pos |>> MatchFalse |> pos
    let valConEnd = (skipChar '(' >>. ws >>. (separatedList pattern ',' |> pos) .>> ws .>> skipChar ')') .>> ws
    let valConPattern =
        pipe2
            (pos id .>> ws)
            valConEnd
            (fun (posn, name) innerPattern ->
                MatchValCon {name=(posn, Choice1Of2 name); innerPattern=innerPattern}) |> pos
    let valConModQualPattern =
        pipe2
            (pos moduleQualifier .>> ws)
            valConEnd
            (fun (posm, modQual) innerPattern ->
                MatchValCon {name=(posm, Choice2Of2 modQual); innerPattern=innerPattern}) |> pos
    let underscorePattern = skipChar '_' |> pos |>> MatchUnderscore |> pos
    let recordPattern = (skipChar '{' >>. ws >>. (separatedList (pos id .>>. (ws >>. skipString ":=" >>. pattern .>> ws)) ',' |> pos .>> ws .>> skipChar '}' .>> ws)) |>> MatchRecCon |> pos
    let unitPattern = skipString "()" |> pos |>> MatchUnit |> pos
    let parensPattern = betweenChar '(' pattern ')'
    let tuplePattern = betweenChar '(' (separatedList pattern ',') ')' |> pos |>> MatchTuple |> pos
    patternRef := choice ([attempt floatPattern; intPattern; truePattern;
                          falsePattern; attempt valConPattern; attempt valConModQualPattern;
                          underscorePattern; recordPattern; unitPattern;
                          attempt tuplePattern; parensPattern; varPattern]) <?> "Pattern"

let functionClause delimiter =
    let arguments =
        betweenChar
            '('
            (separatedList
                ((pipe3'
                    (opt (((attempt (pos (skipString "mut") .>> ws1)) |>> MutAnn) <|> (((attempt (pos (skipString "inout") .>> ws1))) |>> InOutAnn)))
                    (pos id .>> ws)
                    (opt (skipChar ':' >>. ws >>. tyExpr))
                    (fun maybeMut argName maybeArgTyp -> (maybeMut, argName, maybeArgTyp))) |> pos)
                ',')
            ')'
        .>> ws
    let returnTy = opt (skipChar ':' >>. ws >>. tyExpr .>> ws) .>> ws
    let constraintType = choice [(skipString "num" |> pos |>> IsNum);
                                 (skipString "int" |> pos |>> IsInt);
                                 (skipString "real" |> pos |>> IsReal);
                                 attempt (pos record) |>> HasFields;
                                 (skipString "packed") |> pos |>> IsPacked]
    let interfaceConstraints =
        (skipString "where" >>. ws >>. (separatedList (pos (tyExpr .>> ws .>> skipChar ':' .>> ws .>>. pos constraintType) .>> ws) ',') .>> ws) |> opt |>> Option.flattenList |> pos
    (pipe4'
        (attempt (pos arguments))
        (attempt returnTy)
        (attempt interfaceConstraints)
        ((attempt (skipString delimiter)) >>? ws >>? (fatalizeAnyError expr))
        (fun a r c b ->
            {returnTy = r; arguments = a; body = b; interfaceConstraints=c})) <?> "Function clause"

// leftRecursiveExp
let leftRecursiveExp =
    let callArg =
        ((attempt ((pstring "inout") .>> ws1)) >>. fatalizeAnyError (exprws |>> (ConvertAst.convertToLHS "Illegal expression inside inout parameter. The argument must be a left hand side expression."))) |>> InOutArg <|>
        (exprws |>> ExprArg)
    let callArgs = betweenChar '(' (separatedList callArg ',' |> pos) ')' |>> CallArgs <?> "Function call"
    let arrayIndex = betweenChar '[' exprws ']' |>> ArrayIndex <?> "Array access ([])"
    let typeConstraint = skipChar ':' >>. ws >>. tyExpr |>> TypeConstraintType <?> "Type constraint (:)"
    let fieldAccessName = attempt (skipChar '.' >>. notFollowedBy (skipChar '.')) >>. ws >>. id |> pos |>> FieldAccessName <?> "Record field access (.)"
    let refFieldAccessName = skipString "->" >>. ws >>. id |> pos |>> RefFieldAccessName <?> "Record ref field access (->)"
    (([callArgs; arrayIndex; typeConstraint; refFieldAccessName; fieldAccessName] |> choice |> pos .>> wsNoNewline) |> many) <?> "Expression chain (function call, array access, type constraint, field access or ref field access)"

let inlineCpp =
    let normalCharSnippet = manySatisfy (fun c -> c <> '\\' && c <> '#')
    let escapedChar = pstring "\\" >>. (anyOf "\\#" |>> string)
    (between (pstring "#") (pstring "#") (fatalizeAnyError (stringsSepBy normalCharSnippet escapedChar)) |> pos) <?> "Inline C++"

// Debugging utility for some parser p. p |>> printPos will print the position of what
// was parsed by p, assuming that p parses a PosAdorned expression
let printPos expr =
    let pos = getPos expr
    printfn "%s" ((errStr [pos] "Here").Force() |> List.map (fun msg ->
                                                                let ((ErrMsg s) | (PosMsg s)) = msg
                                                                s) |> String.concat "\n\n")
    expr

// expr
do
    let punit = skipString "()" |> pos |>> UnitExp
    let parens = betweenChar '(' (exprws |>> unwrap) ')'
    let ptrue = skipString "true" |> pos |>> TrueExp
    let pfalse = skipString "false" |> pos |>> FalseExp

    // Parsers for operation enclosed parenthesis
    // These operations are syntax sugar for Prelude module functions
    let genParensOp symbol funName = skipString ("(" + symbol + ")") |> pos |>> (fun (pos, _) -> ModQualifierExp (pos, {module_=(pos, "Prelude"); name=(pos, funName)}))
    // For example, (==) gets mapped to Prelude:eq
    let pParensEq = genParensOp "==" "eq"
    let pParensNeq = genParensOp "!=" "neq"
    let pParensGeq = genParensOp ">=" "geq"
    let pParensGt = genParensOp ">" "gt"
    let pParensLeq = genParensOp "<=" "leq"
    let pParensLt = genParensOp "<" "lt"
    let pParensNot = genParensOp "!" "notf"
    let pParensAnd = genParensOp "&&" "andf"
    let pParensOr = genParensOp "||" "orf"
    let pParensAdd = genParensOp "+" "add"
    let pParensSub = genParensOp "-" "sub"
    let pParensMul = genParensOp "*" "mul"
    let pParensDiv = genParensOp "/" "div"
    
    let pfloating = (floatParser .>>. choice [skipChar 'f' >>. preturn FloatExp; preturn DoubleExp]) |>
                    pos |>>
                    (fun (posN, (num, constructor)) -> constructor (posN, num))
    let parseInt s t = skipString s >>. preturn t
    let pint = (pint64 .>>.
                    choice [parseInt "i8" Int8Exp; parseInt "i16" Int16Exp; parseInt "i32" Int32Exp;
                            parseInt "i64" Int64Exp; parseInt "u8" UInt8Exp; parseInt "u16" UInt16Exp;
                            parseInt "u32" UInt32Exp; parseInt "u64" UInt64Exp; preturn IntExp]) |>
               pos |>>
               (fun (posN, (num, constructor)) -> constructor (posN, num))
    let charlist = pos (stringLiteral '\'' true) |>> CharListLiteral
    let str = pos (stringLiteral '"' true) |>> StringLiteral
    // TODO: Somehow get the seq parser to enforce newlines between expressions
    // All attempts so far have either failed or resulted in terrible error messages
    let seq = betweenChar '{' (((expr .>> ws) .>>. fatalizeAnyError (many (expr .>> ws))) |> pos) '}' |>> (fun (overallPos, (firstExpr, restExprs)) -> SequenceExp (overallPos, firstExpr::restExprs))
    let quit = skipString "quit" >>. ws >>. (fatalizeAnyError (opt (skipChar '<' >>. ws >>. tyExpr .>> ws .>> skipChar '>') .>> ws .>> skipChar '(' .>> ws .>> skipChar ')')) |>> QuitExp
    let pIf =
        pipe3
            ((attempt (skipString "if" >>. ws1)) >>. fatalizeAnyError (exprws) .>> ws)
            (fatalizeAnyError expr)
            ((attempt (ws >>. skipString "else" >>. ws1) >>. (fatalizeAnyError expr)) |> opt)
            (fun condition trueBranch maybeFalseBranch ->
                match maybeFalseBranch with
                | Some falseBranch ->
                    IfElseExp {
                        condition = condition;
                        trueBranch = trueBranch;
                        falseBranch = falseBranch
                    }
                | None ->
                    IfExp {
                        condition = condition;
                        trueBranch = trueBranch
                    })
    let pLet =
        pipe2
            ((attempt (pstring "let" >>. ws1)) >>. fatalizeAnyError (pattern .>> ws .>> skipChar '=' .>> ws))
            (fatalizeAnyError expr)
            (fun pat expr ->
                LetExp {left=pat; right=expr})
    let pVar =
        pipe2
            ((attempt (pstring "var" >>. ws1)) >>. fatalizeAnyError (pos id .>> ws))
            (opt (skipChar ':' >>. ws >>. tyExpr))
            (fun varName ty ->
                DeclVarExp { varName = varName; typ = ty} )
    let forInLoop =
        pipe5'
            (attempt (pstring "for" >>. ws1 >>. pos id .>> ws))
            (attempt (skipChar ':' >>. ws >>. tyExpr .>> ws |> opt))
            (attempt (pstring "in" >>. ws1) >>. (fatalizeAnyError (expr .>> ws .>> skipString ".." .>> ws)))
            (fatalizeAnyError (expr .>> ws))
            (fatalizeAnyError expr)
            (fun varName typ start end_ body ->
                ForInLoopExp {varName=varName; typ=typ; start=start; end_=end_; body=body})
    let forLoop =
        pipe4'
            (attempt (pstring "for") >>. ws1 >>. fatalizeAnyError (expr .>> ws .>> skipChar ';' .>> ws))
            (fatalizeAnyError (expr .>> ws .>> skipChar ';' .>> ws))
            (fatalizeAnyError (expr .>> ws1))
            (fatalizeAnyError expr)
            (fun initLoop loopCondition loopStep body ->
                ForLoopExp {initLoop = initLoop; loopCondition = loopCondition; loopStep = loopStep; body = body})
    let doWhileLoop =
        pipe2
            (attempt (pstring "do" >>. ws1) >>. fatalizeAnyError (exprws))
            (fatalizeAnyError (pstring "while" >>. ws1 >>. expr))
            (fun body condition -> DoWhileLoopExp {body=body; condition=condition})
    let whileLoop =
        pipe2'
            (attempt (pstring "while" >>. ws1) >>. fatalizeAnyError (expr .>> ws))
            (fatalizeAnyError expr)
            (fun condition body -> WhileLoopExp {condition=condition; body=body})
    let fn = (pos (functionClause "=>") .>> ws) |>> (fun (posc, clause) -> LambdaExp (posc, clause))
    let match_ =
        let matchClause = (pattern .>> ws) .>>. (pstring "=>" >>. ws >>. exprws)
        pipe2
            (attempt (pstring "match" >>. ws1) >>. fatalizeAnyError (exprws .>> pstring "{" .>> ws))
            (fatalizeAnyError (many1 (matchClause .>> ws)) |> pos .>> ws .>> pstring "}")
            (fun on clauses ->
                MatchExp {on=on; clauses=clauses})
    let fieldp = (pos id .>> ws) .>>. (skipString ":=" >>. ws >>. exprws)
    let recordExpr1 =
        pipe2
            ((skipString "packed") |> pos |> opt .>> ws)
            (betweenChar '{' (ws >>. (fieldp |>> fun field -> [field]) .>> ws) '}' |> pos)
            (fun packed fields ->
                RecordExp {packed=packed; initFields=fields})
    let recordExprMany =
        let fieldList = separatedList1 ((pos id .>> ws) .>>. (skipString ":=" >>. ws >>. exprws)) ','
        pipe2
            ((skipString "packed") |> pos |> opt .>> ws)
            ((attempt (skipChar '{' >>. ws >>. ((fieldp .>> ws .>> skipChar ',' .>> ws)))) .>>. (fatalizeAnyError (fieldList .>> ws .>> skipChar '}')) |> pos)
            (fun packed (fieldsPos, (firstField, remainingFields)) ->
                RecordExp {packed=packed; initFields=(fieldsPos, firstField::remainingFields)})
    let arrayLiteral = betweenChar '[' (separatedList exprws ',') ']' |> pos |>> ArrayLitExp
    let pref = (attempt (pstring "ref" >>. ws1)) >>. (fatalizeAnyError expr) |>> RefExp
    let modQual = moduleQualifier |> pos |>> ModQualifierExp
    let varReference = attempt id |> pos |>> VarExp
    let inlineCpp' = inlineCpp |>> InlineCode
    let tuple = betweenChar '(' (separatedList1 exprws ',') ')' |>> TupleExp
    let smartpointer = (skipString "smartpointer" >>. ws >>. fatalizeAnyError ((skipChar '(' >>. exprws .>> ws .>> skipChar ',' .>> ws) .>>. (exprws .>> ws .>> skipChar ')'))) |>> Smartpointer
    let nullexp = (skipString "null" |> pos |>> NullExp)
    let sizeofexp = (attempt ((skipString "sizeof") >>. ws)) >>? fatalizeAnyError (betweenChar '(' tyExpr ')') |>> SizeofExp 
    let e = choice ([ptrue; pfalse;
                    pParensEq; pParensNeq; pParensGeq; pParensGt; pParensLeq; pParensLt; pParensNot; pParensAnd; pParensOr; pParensAdd; pParensSub; pParensMul; pParensDiv;
                    nullexp; charlist; str;
                    attempt pfloating; pint; smartpointer; sizeofexp;
                    fn; punit; attempt parens; quit; attempt tuple; attempt recordExpr1; recordExprMany; seq;
                    attempt modQual; forInLoop; forLoop; doWhileLoop; whileLoop;
                    pLet; pVar; pIf; match_;
                    arrayLiteral; pref; inlineCpp'; varReference]) |> pos .>> wsNoNewline
    opp.TermParser <-
        (leftRecurse
            (e <?> "Expression")
            leftRecursiveExp
            (fun term chainElem ->
                match chainElem with
                | CallArgs args -> CallExp {func=term; args=args}
                | ArrayIndex index -> ArrayAccessExp {array=term; index=index}
                | TypeConstraintType typ -> TypeConstraint {exp=term; typ=typ}
                | FieldAccessName fieldName -> RecordAccessExp {record=term; fieldName=fieldName}
                | RefFieldAccessName fieldName -> RefRecordAccessExp {recordRef=term; fieldName=fieldName})) <?> "Expression"

// templateApply
do
    templateApplyRef :=
        skipChar '<' >>. ws >>. ((separatedList1 (tyExpr .>> ws) ',') |> pos |> pos) .>> ws .>> skipChar '>'

let functionDec =
    let funName = skipString "fun" >>. ws >>. pos id
    let clause = functionClause "=" |> pos
    (pipe2 (funName .>> ws) clause
        (fun n c ->
            FunctionDec {
                name = n;
                clause = c
            })) <?> "Function declaration"

let moduleName = (skipString "module" >>. ws >>. pos id .>> ws |>> ModuleNameDec) <?> "Module name declaration"

let aliasDec =
    (pipe3
        (skipString "alias" >>. ws >>. pos id .>> ws)
        (templateDec |> opt .>> ws .>> skipChar '=' .>> ws)
        (tyExpr .>> ws)
        (fun name template typ ->
            AliasDec {name=name; template=template; typ=typ})) <?> "Alias declaration"

let adtDec =
    let valueConstructor = (pos id .>> ws .>>. (betweenChar '(' (separatedList (tyExpr .>> ws) ',') ')') .>> ws) <?> "Value constructor"
    (pipe3
        (skipString "type" >>. ws >>. pos id .>> ws)
        (templateDec |> opt .>> ws .>> skipChar '=' .>> ws)
        (separatedList valueConstructor '|' |> pos)
        (fun name template valCons ->
            AlgDataTypeDec {name=name; template=template; valCons=valCons})) <?> "Algebraic datatype declaration"

let letDec =
    (pipe4
        (skipString "let" >>. ws1 >>. ((((skipString "mut" .>> ws1) |> opt |>> Option.isSome |> pos))))
        (pos id .>> ws)
        (skipChar ':' >>. ws >>. tyExpr |> opt .>> ws)
        (skipChar '=' >>. ws >>. exprws)
        (fun mutable_ name typ right ->
            LetDec {varName=name; mutable_=mutable_; typ=typ; right=right})) <?> "Let declaration"

let openDec = (skipString "open" >>. ws >>. skipChar '(' >>. ws >>. (separatedList (pos id) ',' |> pos) .>>
                ws .>> skipChar ')' .>> ws |>> OpenDec) <?> "Open declaration"

let includeDec = (skipString "include" >>. ws >>. skipChar '(' >>. ws >>. separatedList (pos (stringLiteral '"' false)) ',' |> pos .>>
                    ws .>> skipChar ')' .>> ws |>> IncludeDec) <?> "Include declaration"

let inlineCppDec = (inlineCpp .>> ws |>> InlineCodeDec) <?> "Inline C++ (#)"

let program =
    let declarationTypes = [functionDec; moduleName; adtDec; aliasDec; letDec; openDec; includeDec; inlineCppDec]
    ws >>. many (choice declarationTypes |> pos .>> ws) .>> eof