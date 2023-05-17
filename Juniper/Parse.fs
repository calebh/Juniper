module Parse
open FParsec
open Ast
open Extensions

let fatalizeAnyError (p : Parser<'a, 'u>) : Parser<'a, 'u> =
    fun stream ->
        let reply = p stream
        if reply.Status = Ok then
            reply
        else
            Reply(FatalError, reply.Error)

let singleLineComment = skipString "//" >>. restOfLine true >>% ()
let multiLineComment = skipString "/*" >>. skipCharsTillString "*/" true System.Int32.MaxValue
let ws = spaces .>> (choice [singleLineComment; multiLineComment] >>. spaces |> many)
let ws1 = (spaces1 <|> singleLineComment <|> multiLineComment) .>> spaces .>> (choice [singleLineComment; multiLineComment] >>. spaces |> many)

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

type LeftRecursiveExp = CallArgs of PosAdorn<PosAdorn<Expr> list>
                      | ArrayIndex of PosAdorn<Expr>
                      | TypeConstraintType of PosAdorn<TyExpr>
                      | FieldAccessName of PosAdorn<string>
                      | UnsafeTypeCastType of PosAdorn<TyExpr>

type LeftRecursiveTyp = ArrayTyCap of PosAdorn<CapacityExpr>
                      | RefTyRef of PosAdorn<unit>
                      | ApplyTyTemplate of PosAdorn<TemplateApply>

type LeftRecursiveLeftAssign = ArrayMutationIndex of PosAdorn<Expr>
                             | RecordMutationField of PosAdorn<string>

let (templateApply, templateApplyRef) = createParserForwardedToRef()
let (pattern, patternRef) = createParserForwardedToRef()

let opp = new OperatorPrecedenceParser<PosAdorn<Expr>, Position, unit>()
let expr = opp.ExpressionParser

let capOpp = new OperatorPrecedenceParser<PosAdorn<CapacityExpr>, Position, unit>()
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
    infix "||"  2 LogicalOr Associativity.Left;
    infix "&&" 3 LogicalAnd Associativity.Left;
    infix "|" 4 BitwiseOr Associativity.Left;
    infix "^" 5 BitwiseXor Associativity.Left;
    infix "&" 6 BitwiseAnd Associativity.Left;
    infix "=="  7 Equal Associativity.Left;
    infix "!="  7 NotEqual Associativity.Left;
    infix "<"   8 Less Associativity.None;
    infix ">"   8 Greater Associativity.None;
    infix "<="  8 LessOrEqual Associativity.None;
    infix ">="  8 GreaterOrEqual Associativity.None;
    infix ">>" 9 BitshiftRight Associativity.Left;
    infix "<<" 9 BitshiftLeft Associativity.Left;
    infix "+"   10 Add Associativity.Left;
    infix "-"   10 Subtract Associativity.Left;
    infix "*"   11 Multiply Associativity.Left;
    infix "/"   11 Divide Associativity.Left;
    infix "%"   11 Modulo Associativity.Left]

List.iter
    (fun f -> f (fun op term -> UnaryOpExp {op=op; exp=term}) opp)
    [prefix "-"  12 Negate;
    prefix "~" 12 BitwiseNot;
    prefix "!" 12 LogicalNot;
    prefix "*" 12 Deref]

List.iter
    (fun f -> f (fun l op r -> CapacityOp {left=l; op=op; right=r}) capOpp)
    [infix "+" 10 CapAdd Associativity.Left;
    infix "-"  10 CapSubtract Associativity.Left;
    infix "*"  11 CapMultiply Associativity.Left;
    infix "/"  11 CapDivide Associativity.Left]

List.iter
    (fun f -> f (fun op term -> CapacityUnaryOp {op=op; term=term}) capOpp)
    [prefix "-" 11 CapNegate]

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
    pipe2
        // Parse type variables
        (skipChar '<' >>. ws >>. (separatedList (pos id) ',' |> pos))
        // Parse capacity variables
        (ws >>. opt (skipChar ';' >>. ws >>. (separatedList (pos id) ',') |> pos) .>> ws .>> skipChar '>')
        (fun tyVars capVars ->
            {tyVars = tyVars; capVars = capVars})

// capExpr
let capExpr = capOpp.ExpressionParser

do
    let capVar = pos id |>> CapacityNameExpr |> pos
    let capConst = pos pint64 |>> CapacityConst |> pos
    let capParens = skipChar '(' >>. ws >>. capExpr .>> ws .>> skipChar ')'
    capOpp.TermParser <- (choice [capVar; capConst; capParens]) .>> ws

let tyExpr = typOpp.ExpressionParser

let record =
    pipe2
        ((skipString "packed" |> pos |> opt) .>> ws .>> skipChar '{' .>> ws)
        (separatedList ((pos id .>> ws .>> skipChar ':' .>> ws) .>>. tyExpr) ',' |> pos .>> ws .>> skipChar '}' .>> ws)
        (fun packed fields -> { packed=packed; fields=fields })

// leftRecursiveTyp
let leftRecursiveTyp =
    let openBracket = skipChar '[' >>. ws
    let closingBracket = ws >>. skipChar ']' >>. ws
    let arrayTyCap = between openBracket closingBracket capExpr |>> ArrayTyCap
    let refTyRef = pstring "ref" >>. ws >>% () |> pos |>> RefTyRef
    let applyTyTemplate = templateApply .>> ws |>> ApplyTyTemplate
    (choice [arrayTyCap; refTyRef; applyTyTemplate]) |> pos |> many

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
            | "pointer" -> BaseTy (p, TyPointer)
            | "string" -> BaseTy (p, TyString)
            | "rawpointer" -> BaseTy (p, TyRawPointer)
            | _ -> NameTy (p, n))
    let underscore = skipChar '_' |> pos |>> UnderscoreTy
    let mQual = moduleQualifier |>> ModuleQualifierTy
    let closureTy = betweenChar '|' (separatedList ((pos id .>> ws .>> skipChar ':' .>> ws) .>>. tyExpr) ';') '|' |> pos |>> ClosureTy
    let fn =
        pipe3
            (* If the user does not enter a closure type for this function signature,
               assume the user intended the closure to be a type wildcard. *)
            (((betweenChar '(' (choice [name; closureTy; underscore]) ')') |> opt) |> pos)
            (skipChar '(' >>. separatedList (ws >>. tyExpr .>> ws) ',' .>> skipChar ')' .>> ws .>> skipString "->" .>> ws)
            tyExpr
            (fun closure argTys retTy ->
                let closure' =
                    match unwrap closure with
                    | Some c -> (getPos closure, c)
                    // No closure was explicitly given. Desugar into a wildcard (underscore)
                    | None -> (getPos closure, UnderscoreTy (getPos closure, ()))
                FunTy { closure=closure'; args = argTys; returnType = retTy})
    let parens = skipChar '(' >>. ws >>. tyExpr .>> ws .>> skipChar ')' |>> ParensTy
    let recordTy = record |> pos |>> RecordTy
    let t = choice ([attempt mQual; closureTy; attempt recordTy; attempt underscore; name; attempt fn; parens]) |> pos .>> ws
    typOpp.TermParser <-
        leftRecurse
            t
            leftRecursiveTyp
            (fun term chainElem ->
                match chainElem with
                | ArrayTyCap cap -> ArrayTy {valueType=term; capacity=cap}
                | RefTyRef _ -> RefTy term
                | ApplyTyTemplate template -> ApplyTy {tyConstructor=term; args=template})

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
                    let d =
                        if result.IsDecimal then
                            System.Double.Parse(result.String, System.Globalization.CultureInfo.InvariantCulture)
                        elif result.IsHexadecimal then
                            floatOfHexString result.String
                        elif result.IsInfinity then
                            if result.HasMinusSign then System.Double.NegativeInfinity else System.Double.PositiveInfinity
                        else
                            System.Double.NaN
                    Reply(d)
                with 
                | :? System.OverflowException ->
                    Reply(if result.HasMinusSign then System.Double.NegativeInfinity else System.Double.PositiveInfinity)
                | :? System.FormatException ->
                    stream.Skip(-result.String.Length)
                    Reply(FatalError, messageError "The floating-point number has an invalid format (this error is unexpected, please report this error message to fparsec@quanttec.com).")
        else
            Reply(reply.Status, reply.Error)

// Pattern
do
    let varPattern =
        pipe3
            (pstring "mutable" |> opt |>> Option.isSome |> pos .>> ws)
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
    let recordPattern = (skipChar '{' >>. ws >>. (separatedList (pos id .>>. (ws >>. skipChar '=' >>. pattern .>> ws)) ',' |> pos .>> ws .>> skipChar '}' .>> ws)) |>> MatchRecCon |> pos
    let unitPattern = skipString "()" |> pos |>> MatchUnit |> pos
    let parensPattern = betweenChar '(' pattern ')'
    let tuplePattern = betweenChar '(' (separatedList pattern ',') ')' |> pos |>> MatchTuple |> pos
    patternRef := choice ([attempt floatPattern; intPattern; truePattern;
                          falsePattern; attempt valConPattern; attempt valConModQualPattern;
                          underscorePattern; recordPattern; unitPattern;
                          attempt tuplePattern; parensPattern; varPattern])

// leftRecursiveLeftAssign
let leftRecursiveLeftAssign =
    let arrayMutationIndex = betweenChar '[' expr ']' |>> ArrayMutationIndex
    let recordMutationField = skipChar '.' >>. pos id |>> RecordMutationField
    choice [arrayMutationIndex; recordMutationField] |> pos .>> ws |> many

let leftAssign =
    let varMutation = id |> pos |>> VarMutation
    let modQualifierMutation = moduleQualifier |> pos |>> ModQualifierMutation
    let term = (varMutation <|> modQualifierMutation) |> pos .>> ws
    leftRecurse
        term
        leftRecursiveLeftAssign
        (fun term chainElem ->
            match chainElem with
            | ArrayMutationIndex index -> ArrayMutation {array=term; index=index}
            | RecordMutationField fname -> RecordMutation {record=term; fieldName=fname})

let functionClause delimiter =
    let arguments = betweenChar '(' (separatedList (pos id .>>. opt (ws >>. skipChar ':' >>. ws >>. tyExpr)) ',' |> pos) ')' .>> ws
    let returnTy = opt (skipChar ':' >>. ws >>. tyExpr .>> ws) .>> ws
    let constraintType = choice [(skipString "num" |> pos |>> IsNum);
                                 (skipString "int" |> pos |>> IsInt);
                                 (skipString "real" |> pos |>> IsReal);
                                 attempt (pos record) |>> HasFields;
                                 (skipString "packed") |> pos |>> IsPacked]
    let interfaceConstraints =
        (skipString "where" >>. ws >>. (separatedList (pos (tyExpr .>> ws .>> skipChar ':' .>> ws .>>. pos constraintType) .>> ws) ',') .>> ws) |> opt |>> Option.flattenList |> pos
    let body = skipString delimiter >>. ws >>. expr
    pipe4 arguments returnTy interfaceConstraints body
        (fun a r c b ->
            {returnTy = r; arguments = a; body = b; interfaceConstraints=c})

// leftRecursiveExp
let leftRecursiveExp =
    let callArgs = betweenChar '(' (separatedList expr ',' |> pos) ')' |>> CallArgs
    let arrayIndex = betweenChar '[' expr ']' |>> ArrayIndex
    let typeConstraint = skipChar ':' >>. ws >>. tyExpr |>> TypeConstraintType
    let fieldAccessName = skipChar '.' >>. ws >>. id |> pos |>> FieldAccessName
    let unsafeTypeCast = skipString "::::" >>. ws >>. tyExpr |>> UnsafeTypeCastType
    [callArgs; arrayIndex; unsafeTypeCast; typeConstraint; fieldAccessName] |> choice |> pos .>> ws |> many

let inlineCpp =
    let normalCharSnippet = manySatisfy (fun c -> c <> '\\' && c <> '#')
    let escapedChar = pstring "\\" >>. (anyOf "\\#" |>> string)
    between (pstring "#") (pstring "#") (fatalizeAnyError (stringsSepBy normalCharSnippet escapedChar)) |> pos

// expr
do
    let punit = skipString "()" |> pos |>> UnitExp
    let parens = betweenChar '(' (expr |>> unwrap) ')'
    let ptrue = skipString "true" |> pos |>> TrueExp
    let pfalse = skipString "false" |> pos |>> FalseExp
    
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
    let seq = betweenChar '{' (((expr .>> ws .>> skipChar ';' .>> ws) .>>. fatalizeAnyError (many (expr .>> ws .>> skipChar ';' .>> ws))) |> pos) '}' |>> (fun (overallPos, (firstExpr, restExprs)) -> SequenceExp (overallPos, firstExpr::restExprs))
    let quit = skipString "quit" >>. ws >>. (fatalizeAnyError (opt (skipChar '<' >>. ws >>. tyExpr .>> ws .>> skipChar '>') .>> ws .>> skipChar '(' .>> ws .>> skipChar ')')) |>> QuitExp
    let pIf =
        pipe3
            ((attempt (skipString "if" >>. ws)) >>. skipChar '(' >>. ws >>. fatalizeAnyError (expr .>> ws) .>> ws .>> skipChar ')' .>> ws)
            (fatalizeAnyError (expr .>> ws))
            (fatalizeAnyError (skipString "else" >>. ws >>. expr .>> ws))
            (fun condition trueBranch falseBranch ->
                IfElseExp {
                    condition = condition;
                    trueBranch = trueBranch;
                    falseBranch = falseBranch
                })
    let pLet =
        pipe2
            ((attempt (pstring "let" >>. ws1)) >>. fatalizeAnyError (pattern .>> ws .>> skipChar '=' .>> ws))
            (fatalizeAnyError (expr .>> ws))
            (fun pat expr ->
                LetExp {left=pat; right=expr})
    let pVar =
        pipe2
            ((attempt (pstring "var" >>. ws1)) >>. fatalizeAnyError (pos id .>> ws))
            (fatalizeAnyError (skipChar ':' >>. ws >>. tyExpr))
            (fun varName ty ->
                DeclVarExp { varName = varName; typ = ty} )
    let assign =
        pipe3
            ((attempt (skipString "set" >>. ws1)) >>. (fatalizeAnyError (skipString "*" |> opt |>> Option.isSome |> pos) .>> ws))
            (fatalizeAnyError (leftAssign .>> ws .>> skipChar '=' .>> ws))
            (fatalizeAnyError expr)
            (fun ref_ left right -> AssignExp {left=left; right=right; ref=ref_})
    let forLoop =
        pipe6
            ((attempt (pstring "for" >>. ws1)) >>. fatalizeAnyError (pos id .>> ws))
            (fatalizeAnyError (skipChar ':' >>. ws >>. tyExpr .>> ws |> opt))
            (fatalizeAnyError (pstring "in" >>. ws >>. expr .>> ws))
            (fatalizeAnyError ((pstring "to" >>% Upto) <|> (pstring "downto" >>% Downto) |> pos .>> ws))
            (fatalizeAnyError expr)
            (fatalizeAnyError (pstring "do" >>. ws >>. expr .>> pstring "end"))
            (fun varName typ start direction end_ body ->
                ForLoopExp {varName=varName; typ=typ; start=start; direction=direction; end_=end_; body=body})
    let doWhileLoop =
        pipe2
            (attempt (pstring "do" >>. ws1) >>. fatalizeAnyError (expr .>> ws))
            (fatalizeAnyError (pstring "while" >>. ws >>. expr .>> ws .>> pstring "end"))
            (fun body condition -> DoWhileLoopExp {body=body; condition=condition})
    let whileLoop =
        pipe2
            (attempt (pstring "while" >>. ws1) >>. fatalizeAnyError (expr .>> ws .>> pstring "do" .>> ws))
            (fatalizeAnyError (expr .>> ws .>> pstring "end"))
            (fun condition body -> WhileLoopExp {condition=condition; body=body})
    let fn = (attempt (skipString "fn" >>. ws1)) >>. fatalizeAnyError (functionClause "->" .>> ws .>> skipString "end") |> pos |>> LambdaExp
    let match_ =
        let matchClause = (pattern .>> ws) .>>. (pstring "=>" >>. ws >>. expr)
        pipe2
            (attempt (pstring "match" >>. ws1) >>. fatalizeAnyError (expr .>> pstring "{" .>> ws))
            (fatalizeAnyError (sepBy1 (matchClause .>> ws) (skipString "," .>> ws)) |> pos .>> ws .>> pstring "}" .>> ws)
            (fun on clauses ->
                CaseExp {on=on; clauses=clauses})
    let fieldp = (pos id .>> ws) .>>. (skipChar '=' >>. ws >>. expr)
    let recordExpr1 =
        pipe2
            ((skipString "packed") |> pos |> opt .>> ws)
            (betweenChar '{' (ws >>. (fieldp |>> fun field -> [field]) .>> ws) '}' |> pos)
            (fun packed fields ->
                RecordExp {packed=packed; initFields=fields})
    let recordExprMany =
        let fieldList = separatedList1 ((pos id .>> ws) .>>. (skipChar '=' >>. ws >>. expr)) ','
        pipe2
            ((skipString "packed") |> pos |> opt .>> ws)
            ((attempt (skipChar '{' >>. ws >>. ((fieldp .>> ws .>> skipChar ',' .>> ws)))) .>>. (fatalizeAnyError (fieldList .>> ws .>> skipChar '}' .>> ws)) |> pos)
            (fun packed (fieldsPos, (firstField, remainingFields)) ->
                RecordExp {packed=packed; initFields=(fieldsPos, firstField::remainingFields)})
    let arrayLiteral = betweenChar '[' (separatedList expr ',') ']' |> pos |>> ArrayLitExp
    let pref = (attempt (pstring "ref" >>. ws1)) >>. (fatalizeAnyError expr) |>> RefExp
    let modQual = moduleQualifier |> pos |>> ModQualifierExp
    let varReference = attempt id |> pos |>> VarExp
    let arrayMake =
        pipe2
            (skipString "array" >>. ws >>. fatalizeAnyError (tyExpr .>> ws))
            (fatalizeAnyError ((skipString "of" >>. ws >>. expr |> opt) .>> ws .>> skipString "end"))
            (fun arrTy initializer -> ArrayMakeExp {typ=arrTy; initializer=initializer})
    let inlineCpp' = inlineCpp |>> InlineCode
    let tuple = betweenChar '(' (separatedList1 expr ',') ')' |>> TupleExp
    let smartpointer = (skipString "smartpointer" >>. ws >>. fatalizeAnyError ((skipChar '(' >>. expr .>> ws .>> skipChar ',' .>> ws) .>>. (expr .>> ws .>> skipChar ')'))) |>> Smartpointer
    let nullexp = (skipString "null" |> pos |>> NullExp) .>> ws
    //let sizeofexp = skipString "sizeof" >>. ws >>. fatalizeAnyError (betweenChar '(' tyExpr ')') 
    let e = choice ([punit; attempt parens; ptrue; pfalse; nullexp; charlist; str;
                    attempt pfloating; pint; smartpointer;
                    fn; quit; attempt tuple; attempt recordExpr1; recordExprMany; seq;
                    attempt modQual; forLoop; doWhileLoop; whileLoop;
                    pLet; pVar; pIf; assign; match_;
                    arrayLiteral; pref; arrayMake; inlineCpp'; varReference]) .>> ws |> pos
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
                | UnsafeTypeCastType typ -> UnsafeTypeCast {exp=term; typ=typ})

// templateApply
do
    templateApplyRef :=
        pipe2
            (skipChar '<' >>. ws >>. separatedList tyExpr ',' .>> ws |> pos)
            ((((opt (skipChar ';' >>. ws >>. separatedList (capExpr) ','))) |>>
                fun x ->
                    match x with
                    | Some x -> x
                    | None -> []
                |> pos) .>> ws .>> skipChar '>')
            (fun tyExprs capExprs ->
                {tyExprs = tyExprs; capExprs = capExprs}) |> pos

let functionDec =
    let funName = skipString "fun" >>. ws >>. pos id
    let clause = functionClause "=" |> pos
    pipe2 (funName .>> ws) clause
        (fun n c ->
            FunctionDec {
                name = n;
                clause = c
            })

let moduleName = skipString "module" >>. ws >>. pos id .>> ws |>> ModuleNameDec

let aliasDec =
    pipe3
        (skipString "alias" >>. ws >>. pos id .>> ws)
        (templateDec |> pos |> opt .>> ws .>> skipChar '=' .>> ws)
        (tyExpr .>> ws)
        (fun name template typ ->
            AliasDec {name=name; template=template; typ=typ})

let unionDec =
    let valueConstructor = pos id .>> ws .>>. (betweenChar '(' (separatedList (tyExpr .>> ws) ',') ')') .>> ws
    pipe3
        (skipString "type" >>. ws >>. pos id .>> ws)
        (templateDec |> pos |> opt .>> ws .>> skipChar '=' .>> ws)
        (separatedList valueConstructor '|' |> pos)
        (fun name template valCons ->
            UnionDec {name=name; template=template; valCons=valCons})

let letDec =
    pipe3
        (skipString "let" >>. ws >>. pos id .>> ws)
        (skipChar ':' >>. ws >>. tyExpr |> opt .>> ws)
        (skipChar '=' >>. ws >>. expr .>> ws)
        (fun name typ right ->
            LetDec {varName=name; typ=typ; right=right})

let openDec = skipString "open" >>. ws >>. skipChar '(' >>. ws >>. (separatedList (pos id) ',' |> pos) .>>
                ws .>> skipChar ')' .>> ws |>> OpenDec

let includeDec = skipString "include" >>. ws >>. skipChar '(' >>. ws >>. separatedList (pos (stringLiteral '"' false)) ',' |> pos .>>
                    ws .>> skipChar ')' .>> ws |>> IncludeDec

let inlineCppDec = inlineCpp .>> ws |>> InlineCodeDec

let program =
    let declarationTypes = [functionDec; moduleName; unionDec; aliasDec; letDec; openDec; includeDec; inlineCppDec]
    ws >>. many (choice declarationTypes |> pos .>> ws) .>> eof