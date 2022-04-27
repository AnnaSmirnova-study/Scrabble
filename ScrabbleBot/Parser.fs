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

    let (.>*>.) p1 p2 = p1 .>> spaces .>>. p2
    let (.>*>) p1 p2  = p1 .>> spaces .>> p2
    let (>*>.) p1 p2  = p1 .>> spaces >>. p2

    let parenthesise p = pchar '(' >*>. p .>*> pchar ')'

    let pid = 
        let aux ((c,l) : char * char list) = string c + System.String.Concat(l)
        pletter <|> pchar '_' .>>. many palphanumeric |>> aux

    
    let unop p1 p2 = p1 >*>. p2
    let binop po p1 p2 = p1 .>*> po .>*>. p2

    let TermParse, tref = createParserForwardedToRef<aExp>()
    let ProdParse, pref = createParserForwardedToRef<aExp>()
    let AtomParse, aref = createParserForwardedToRef<aExp>()
    let CharParse, cref = createParserForwardedToRef<cExp>()

    let AddParse = binop (pchar '+') ProdParse TermParse |>> Add <?> "Add"
    let SubParse = binop (pchar '-') ProdParse TermParse |>> Sub <?> "Sub"
    do tref := choice [AddParse; SubParse; ProdParse]

    let MulParse = binop (pchar '*') AtomParse ProdParse |>> Mul <?> "Mul"
    let DivParse = binop (pchar '/') AtomParse ProdParse |>> Div <?> "Div"
    let ModParse = binop (pchar '%') AtomParse ProdParse |>> Mod <?> "Mod"
    do pref := choice [MulParse; DivParse; ModParse; AtomParse]
    
    let NParse   = pint32 |>> N <?> "Int"
    let VParse   = pid |>> V <?> "Variable"
    let PVParse   = unop pPointValue AtomParse |>> PV <?> "PointValue"
    let NegParse   = unop (pchar '-') AtomParse |>> (fun x -> Mul (N -1, x)) <?> "Negation"
    let CTIParse   = unop pCharToInt CharParse |>> CharToInt <?> "CharToInt"
    let ParParse = parenthesise TermParse
    do aref := choice [PVParse; CTIParse; NegParse; NParse; VParse; ParParse]

    let CParParse = parenthesise CharParse
    let CVParse   = unop pCharValue AtomParse |>> CV <?> "CharValue"
    let CParse   = pstring "\'" >>. anyChar .>> pstring"\'" |>> C <?> "Char"
    let TUParse   = unop pToUpper CParParse |>> ToUpper <?> "ToUpper"
    let TLParse   = unop pToLower CParParse |>> ToLower <?> "ToLower"
    let ITCParse   = unop pIntToChar TermParse |>> IntToChar <?> "IntToChar"
    do cref := choice [CVParse; TUParse; TLParse; ITCParse; CParse; CParParse]

    let AexpParse = TermParse 

    let CexpParse = CharParse

    let BexpParse = pstring "not implemented"

    let stmntParse = pstring "not implemented"

    (* The rest of your parser goes here *)
    type word   = (char * int) list
    type squareFun = word -> int -> int -> Result<int, Error>
    type square = Map<int, squareFun>
    
    type boardFun2 = coord -> Result<square option, Error>
        
    type board = {
        center        : coord
        defaultSquare : square
        squares       : boardFun2
    }
    
    // Default (unusable) board in case you are not implementing a parser for the DSL.
    let mkBoard : boardProg -> board = fun _ -> {center = (0,0); defaultSquare = Map.empty; squares = fun _ -> Success (Some Map.empty)}
