// ScrabbleUtil contains the types coord, boardProg, and SquareProg. Remove these from your file before proceeding.
// Also note that the modulse Ass7 and ImpParser have been merged to one module called Parser.

// Insert your Parser.fs file here from Assignment 7. All modules must be internal.

module internal Parser

    open StateMonad
    open ScrabbleUtil // NEW. KEEP THIS LINE.
    open System
    open Eval
    open FParsecLight.TextParser     // Industrial parser-combinator library. Use for Scrabble Project.
    
    
    let pIntToChar  = pstring "intToChar"
    let pPointValue = pstring "pointValue"

    let pCharToInt  = pstring "charToInt"
    let pToUpper    = pstring "toUpper"
    let pToLower    = pstring "toLower"
    let pCharValue  = pstring "charValue"

    let pTrue       = pstring "true"
    let pFalse      = pstring "false"
    let pIsDigit    = pstring "isDigit"
    let pIsLetter   = pstring "isLetter"
    let pIsVowel   = pstring "isVowel"

    let pif       = pstring "if"
    let pthen     = pstring "then"
    let pelse     = pstring "else"
    let pwhile    = pstring "while"
    let pdo       = pstring "do"
    let pdeclare  = pstring "declare"

    let whitespaceChar = satisfy (fun c -> System.Char.IsWhiteSpace c) <?> "whitespace"
    let pletter        = satisfy (fun c -> System.Char.IsLetter c) <?> "letter"
    let palphanumeric  = satisfy (fun c -> System.Char.IsLetterOrDigit c) <?> "alphanumeric"

    let spaces         = many whitespaceChar <?> "space"
    let spaces1        = many1 whitespaceChar <?> "space1"

    // Discard whitespaces between p1 and p2
    let (.>*>.) p1 p2 = p1 .>> spaces .>>. p2
    // Return only p1 result
    let (.>*>) p1 p2  = p1 .>> spaces .>> p2
    // Return only p2 result
    let (>*>.) p1 p2  = p1 .>> spaces >>. p2

    // Parse parenthesis to return p result
    let parenthesise p = pchar '(' >*>. p .>*> pchar ')'
    let cbracket p = pchar '{' >*>. p .>*> pchar '}'

    // Parse id starting with letter or _
    let pid = 
        let aux ((c,l) : char * char list) = string c + System.String.Concat(l)
        pletter <|> pchar '_' .>>. many (palphanumeric <|> pchar '_') |>> aux

    // Parse unary operator (operator) (element) and return element 
    let unop po p1 = po >*>. p1
    // Parse binary operator (element) (operator) (element) and return elements
    let binop po p1 p2 = p1 .>*> po .>*>. p2

    // Parse p separated by sep with possible spaces 0/1 or more times and return p list
    let sepByS p sep = sepBy p (spaces >>. sep .>> spaces)
    let sepBy1S p sep = sepBy1 p (spaces >>. sep .>> spaces)



    // Numeric and char parse
    let TermParse, tref = createParserForwardedToRef<aExp>()
    let ProdParse, pref = createParserForwardedToRef<aExp>()
    let AtomParse, aref = createParserForwardedToRef<aExp>()
    let CharParse, cref = createParserForwardedToRef<cExp>()

    // Numeric third priority
    let AddParse = binop (pchar '+') ProdParse TermParse |>> Add <?> "Add"
    let SubParse = binop (pchar '-') ProdParse TermParse |>> Sub <?> "Sub"
    do tref := choice [AddParse; SubParse; ProdParse]

    // Numeric second priority
    let MulParse = binop (pchar '*') AtomParse ProdParse |>> Mul <?> "Mul"
    let DivParse = binop (pchar '/') AtomParse ProdParse |>> Div <?> "Div"
    let ModParse = binop (pchar '%') AtomParse ProdParse |>> Mod <?> "Mod"
    do pref := choice [MulParse; DivParse; ModParse; AtomParse]
    
    // Numeric first priority
    let PVParse   = unop pPointValue (parenthesise TermParse) |>> PV <?> "PointValue"
    let CTIParse   = unop pCharToInt (parenthesise CharParse) |>> CharToInt <?> "CharToInt"
    let NegParse   = unop (pchar '-') AtomParse |>> (fun x -> Mul (N -1, x)) <?> "Negation"
    let NParse   = pint32 |>> N <?> "Int"
    let VParse   = pid |>> V <?> "Variable"
    let ParParse = parenthesise TermParse
    do aref := choice [PVParse; CTIParse; NegParse; NParse; VParse; ParParse]

    // Char parse
    let CVParse   = unop pCharValue (parenthesise TermParse) |>> CV <?> "CharValue"
    let TUParse   = unop pToUpper (parenthesise CharParse) |>> ToUpper <?> "ToUpper"
    let TLParse   = unop pToLower (parenthesise CharParse) |>> ToLower <?> "ToLower"
    let ITCParse   = unop pIntToChar (parenthesise TermParse) |>> IntToChar <?> "IntToChar"
    let CParse   = pstring "\'" >>. anyChar .>> pstring"\'" |>> C <?> "Char"
    do cref := choice [CVParse; TUParse; TLParse; ITCParse; CParse]



    // Binary parse
    let BTermParse, btref = createParserForwardedToRef<bExp>()
    let BAtomParse, baref = createParserForwardedToRef<bExp>()
    let BAEqualityParse, baeref = createParserForwardedToRef<bExp>()

    let BConjParse = sepBy1S BAtomParse (pstring "/\\") |>> List.reduceBack (fun x y -> Conj (x,y)) <?> "Conj"
    let BDisjParse = sepBy1S BAtomParse (pstring "\\/") |>> List.reduceBack (fun x y -> x .||. y) <?> "Disj"
    do btref := choice [BConjParse; BDisjParse; BAtomParse]

    let BNParse = unop (pchar '~') BTermParse |>> Not <?> "Not"
    let BILParse = unop pIsLetter (parenthesise CharParse) |>> IsLetter <?> "IsLetter"
    let BIVParse = unop pIsVowel (parenthesise CharParse) |>> IsVowel <?> "IsVowel"
    let BIDParse = unop pIsDigit (parenthesise CharParse) |>> IsDigit <?> "IsDigit"
    let BTTParse = pTrue |>> (fun _ -> TT) <?> "True"
    let BFFParse = pFalse |>> (fun _ -> FF) <?> "False"
    let BParParse = parenthesise BTermParse
    do baref := choice [BNParse; BILParse; BIVParse; BIDParse; BTTParse; BFFParse; BParParse; BAEqualityParse]

    // Parse equality/difference of two numbers
    let AEqParse = binop (pchar '=') TermParse TermParse |>> AEq <?> "Equality"
    let AIneqParse = binop (pstring "<>") TermParse TermParse |>> (fun (x,y) -> x .<>. y) <?> "Inequality"
    let ALtParse = binop (pchar '<') TermParse TermParse |>> ALt <?> "Less than"
    let ALtEqParse = binop (pstring "<=") TermParse TermParse |>> (fun (x,y) -> x .<=. y) <?> "Less than or equal"
    let AHtParse = binop (pchar '>') TermParse TermParse |>> (fun (x,y) -> x .>. y) <?> "Higher than"
    let AHtEqParse = binop (pstring ">=") TermParse TermParse |>> (fun (x,y) -> x .>=. y) <?> "Higher than or equal"
    do baeref := choice [AEqParse; AIneqParse; ALtParse; ALtEqParse; AHtParse; AHtEqParse]



    // Statement parse
    let SAParse, saref = createParserForwardedToRef<stm>()
    let SBParse, sbref = createParserForwardedToRef<stm>()
    let SCParse, scref = createParserForwardedToRef<stm>()

    let SSeqParse = sepByS SBParse (pchar ';') |>> List.reduceBack (fun x y -> Seq (x,y)) <?> "Seq"
    do saref := choice [SSeqParse; SBParse]

    let SITEParse = unop pif (parenthesise BTermParse) .>*>. unop pthen (cbracket SAParse) .>*>. opt (unop pelse (cbracket SAParse)) |>> (fun ((x,y),zO) -> Option.map (fun z -> ITE (x,y,z)) zO |> Option.defaultValue (ITE (x,y,Skip))) <?> "If-then-(else)"
    let SWDParse = unop pwhile (parenthesise BTermParse) .>*>. unop pdo (cbracket SCParse) |>> While <?> "While-do"
    do sbref := choice [SITEParse; SWDParse; SCParse]

    let SDecParse = pdeclare >>. spaces1 >>. pid  |>> Declare <?> "Declare"
    let SAssParse = binop (pstring ":=") pid TermParse |>> Ass <?> "Assign"
    let SBraParse = cbracket SAParse
    let SParParse = parenthesise SAParse
    do scref := choice [SDecParse; SAssParse; SBraParse; SParParse]



    let AexpParse = TermParse 

    let CexpParse = CharParse

    let BexpParse = BTermParse

    let stmntParse = SAParse

    (* The rest of your parser goes here *)
    type word   = (char * int) list
    type squareFun = word -> int -> int -> Result<int, Error>
    type square = Map<int, squareFun>

    let parseSquareProg sqp : square = Map.map (fun k v -> run stmntParse v |> getSuccess |> stmntToSquareFun) sqp
    
    type boardFun2 = coord -> Result<square option, Error>
        
    type board = {
        center        : coord
        defaultSquare : square
        squares       : boardFun2
    }
    
    let parseBoardFun s m : boardFun2 = run stmntParse s |> getSuccess |> fun stm -> stmntToBoardFun stm m
    
    let mkBoard (bp : boardProg) = 
        let m = Map.map (fun k v -> parseSquareProg v) bp.squares
        {
            center = bp.center;
            defaultSquare = Map.find bp.usedSquare m;
            squares = parseBoardFun bp.prog m
        }
        
    // Default (unusable) board in case you are not implementing a parser for the DSL.
    //let mkBoard : boardProg -> board = fun _ -> {center = (0,0); defaultSquare = Map.empty; squares = fun _ -> Success (Some Map.empty)}
