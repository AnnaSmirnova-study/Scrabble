namespace ScrabbleFighter

open System.Linq
open ScrabbleUtil
open ScrabbleUtil.ServerCommunication
open System.IO

open ScrabbleUtil.DebugPrint


module Print =
    let printHand pieces hand =
        hand |>
        MultiSet.fold (fun _ x i -> forcePrint (sprintf "%d -> (%A, %d)\n" x (Map.find x pieces) i)) ()

module State = 
    // Make sure to keep your state localised in this module. It makes your life a whole lot easier.
    // Currently, it only keeps track of your hand, your player numer, your board, and your dictionary,
    // but it could, potentially, keep track of other useful
    // information, such as number of players, player turn, etc.

    type tileVal = (char * int)
    

    type state = {
        board         : Parser.board
        dict          : ScrabbleUtil.Dictionary.Dict
        players       : Map<uint32,bool>
        changeAllowed : bool
        playerNumber  : uint32
        numPlayers    : uint32
        hand          : MultiSet.MultiSet<uint32>
        tiles         : Map<coord,tileVal>
        playerTurn    : uint32
    }

    let mkPlayersMap numPlayers = List.fold (fun acc i -> Map.add i true acc) Map.empty [1u..numPlayers]

    let mkState b d pmp ca pn np h tiles pt = {
        board = b; 
        dict = d;  
        players = pmp;
        changeAllowed = ca;
        playerNumber = pn; 
        numPlayers = np;
        hand = h; 
        tiles = tiles;
        playerTurn = pt;
    }

    let board st         = st.board
    let dict st          = st.dict
    let playerNumber st  = st.playerNumber
    let numPlayers st    = st.numPlayers
    let hand st          = st.hand
    let playerTurn st    = st.playerTurn

    let updPlayerTurn st =
        let rec t pn = 
            if pn > st.numPlayers then t 1u
            else if st.players[pn] then pn
            else t (pn+1u)
        // To avoid eternal loop if all are false
        if Map.forall (fun _ v -> not v) st.players then 0u
        else t (st.playerTurn+1u)


module internal algorithm =

    type ws = {
        coords   : coord
        sqr      : Parser.square
        pos      : int
        canEnd   : bool
    }

    let mkWS coords sqr pos canEnd = {
        coords = coords;
        sqr = sqr;
        pos = pos;
        canEnd = canEnd;
    }
    
    let tileChar = fun (c,_) -> c

    // Functions to update coordinates
    let right = fun (x,y) -> (x+1,y)
    let left = fun (x,y) -> (x-1,y)
    let up = fun (x,y) -> (x,y-1)
    let down = fun (x,y) -> (x,y+1)

    // Calculate the points in the complete word from the squareFuns
    let calcPoints word sqrs = 
        let f = List.sortBy (fun (_,(k,_)) -> k) (Map.toList sqrs)
        List.fold (fun acc (pos,(_,sf)) -> 
            match sf word pos acc with
            | StateMonad.Success acc' -> acc'
            | _ -> acc) 0 f

    // Given two (points,move) option, returns the one with the greatest amount of points
    let greatest a b =
        match a with
        | Some (p,m) -> 
            match b with
            | Some (p',m') -> if p > p' then Some (p,m) else Some (p',m')
            | None -> Some (p,m)
        | None -> b

    // Add squareFun from a given square to the map of squareFuns
    let addSF pos (sqr:Parser.square) sqrs = Map.fold (fun acc k v -> Map.add pos (k,v) acc) sqrs sqr


    let findWord hand (st:State.state) =

        let rec tryNextLetter squares dictStep hand pos word sqrs move =
            match squares with
            // Square is valid and not free
            | (ws,Some tileVal)::tail -> 
                match Dictionary.step (tileChar tileVal) dictStep with
                | Some (b,dictStep') -> 
                    match tryNextLetter tail dictStep' hand (pos+1) (tileVal::word) (addSF pos ws.sqr sqrs) move with
                    | Some move' -> Some move'
                    | None -> if b && ws.canEnd && not (List.isEmpty move) then Some (calcPoints (List.rev word) sqrs, move) else None
                | None -> None
            // Square is valid and free
            | (ws,None)::tail -> 
                MultiSet.fold (fun mv (id,tile) _ -> 
                    Set.fold (fun mv' tileVal ->
                        match Dictionary.step (tileChar tileVal) dictStep with
                        | Some (b,dictStep') -> 
                            match tryNextLetter tail dictStep' (MultiSet.removeSingle (id,tile) hand) (pos+1) (tileVal::word) (addSF pos ws.sqr sqrs) ((ws.coords,(id,tileVal))::move) with
                            | Some (points,move) -> 
                                match mv' with
                                | Some (points',_) -> if points > points' then Some (points,move) else mv'
                                | None -> Some (points,move)
                            | None -> if b && ws.canEnd then Some (calcPoints (List.rev word) sqrs, (((ws.coords,(id,tileVal))::move))) else mv'
                        | None -> mv'
                    ) mv tile
                ) None hand
            | _ -> None

            
        (*
            Try to start a word from each square in the list (which was made in getSquares)
            sqrsBefore is the reverse list of squares before the square we wish to start from
            sqrsToUse is the lit of squares which may be used in the word

            [][][] <- sqrsBefore  [][][][] <- sqrsToUse
                                  ^ This is the square the word will start from
        
            When trying to start from the next square, move
            [][][]   [][][][]
            ^ This
            [][]   [][][][][]
                   ^ To here
            and try again
        *)
        let rec tryFromNextSquare (sqrsBefore,sqrsToUse) dict hand mv =
            if List.isEmpty sqrsToUse then None
            else
                tryNextLetter sqrsToUse dict hand 0 [] Map.empty [] |>
                greatest mv |>
                fun mv' ->
                    match sqrsBefore with
                    | b::tail -> tryFromNextSquare (tail,b::sqrsToUse) dict hand mv'
                    | _ -> mv'

    
        (* 
            Check if a square is free.
            If the square is free returns Some (Some square, None).
            If the square is not free returns Some (Some square, Some tile)
            Any other result means the square should be treated as invalid, and should not be used
        *)
        let checkSquareTile coords squares = squares coords |> function 
            | StateMonad.Success sqr -> sqr |> Option.map (fun sqr -> sqr) |> fun sqr -> Some (sqr, Map.tryFind coords st.tiles)
            | StateMonad.Failure _ -> None

        // Check if the squares to the right/left or above/below are free
        let sidesFree boardSquares before after coords =
            let check side = 
                match checkSquareTile (side coords) boardSquares with
                | Some (Some _, Some _) -> false
                | _ -> true
            if (check before) && (check after) then true else false

        (* 
            Get a list of the squares before and after the given coordinates where the word may be placed.
            This is done to have a set list of squares, rather than fetching the same squares over and over while creating the word.

            The getSquaresBefore function will get a list of squares before the given coordinates. 
            The list will include a max number of squares equal to "count" (the number of tiles in the hand).
            If the function encounters a used square, neither this square nor the following will be included.
            ['A'][][][][]  <- moving right to left
                   ^ List will stop here
            This ensures the word will to include any letters before the given coordinates.
            If a word can be made with said letter, it will be attempted when checking that tile, so it should not be used here.

            The getSquaresAfter function will include the given coordinates as well as any used square located after the given coordinates.
            The list will include a max number of unused squares equal to "count" (the number of tiles in the hand).
            Any used squares found along the way will not count towards this limit.
            ['A'][][][]['A'][][][][]
              ^ This is the square at the given coordinates

            The value canEnd in the list item signals whether the square is a valin place to end a word.
            The word cannot end on a square if the square is located before the given coordinates, or if it followed by a used square.
        *)
        let getSquares boardSquares count back forward sidesFree coords  =
            let canEnd coords' = 
                match checkSquareTile (forward coords') boardSquares with
                | Some (Some _, Some _) -> false
                | _ -> true

            let rec getSquaresAfter coords' next' count' pos acc = 
                match checkSquareTile coords' boardSquares with
                | Some (Some sqr, None) -> if (count' > 0) && (sidesFree coords') then getSquaresAfter (next' coords') next' (count'-1) (pos+1) (((mkWS coords' sqr pos (canEnd coords')),None)::acc) else acc
                | Some (Some sqr, Some tile) -> getSquaresAfter (next' coords') next' count' (pos+1) (((mkWS coords' sqr pos (canEnd coords')),Some tile)::acc)
                | _ -> acc
            let rec getSquaresBefore coords' next' count' pos acc =
                match checkSquareTile coords' boardSquares with
                | Some (Some sqr, None) -> if (count' > 0) && (sidesFree coords') then getSquaresBefore (next' coords') next' (count'-1) (pos-1) (((mkWS coords' sqr pos false),None)::acc) else acc
                | Some (Some _, Some _) -> acc.Tail
                | _ -> acc
            (List.rev (getSquaresBefore (back coords) back count -1 []), List.rev (getSquaresAfter coords forward count 0 []))


        (*
            Functions for checking directions.
            sidesFree(H/V) are functions to check the squares above/below and left/right of given coordinates.
            squares(H/V) create the square lists horizontally and vertically for the given coordinates.
            try(H/V) runs the algorithm in a horizontal or vertical direction, if the given coordinates are not preceded by a used square (meaning a word cannot start there).
        *)
        let sidesFreeH = sidesFree st.board.squares up down
        let sidesFreeV = sidesFree st.board.squares left right

        let squaresH = getSquares st.board.squares (int (MultiSet.size hand)) left right sidesFreeH
        let squaresV = getSquares st.board.squares (int (MultiSet.size hand)) up down sidesFreeV

        let tryH coords = 
            match checkSquareTile (left coords) st.board.squares with 
            | Some (Some _, Some _) -> None
            | _ -> tryFromNextSquare (squaresH coords) st.dict hand None
        let tryV coords =
            match checkSquareTile (up coords) st.board.squares with 
            | Some (Some _, Some _) -> None
            | _ -> tryFromNextSquare (squaresV coords) st.dict hand None

        if Map.isEmpty st.tiles then greatest (tryH st.board.center) (tryV st.board.center)
        else
            let moves = 
                [for (coords,_) in Map.toSeq st.tiles do yield async { return greatest (tryH coords) (tryV coords) }] |>
                Async.Parallel |>
                Async.RunSynchronously

            Array.reduce (fun a b -> greatest a b) moves


module Scrabble =

    let playGame cstream pieces (st : State.state) =
            
        let rec aux (st : State.state) =
            // Print.printHand pieces (State.hand st)

            if st.playerTurn = st.playerNumber then

                // Waits for input before startung turn (just press enter)
                // let input =  System.Console.ReadLine()

                let hand' = MultiSet.fold (fun acc id count -> 
                                match Map.tryFind id pieces with
                                | Some (t: tile) -> MultiSet.add (id, t) count acc
                                | None -> acc
                                ) MultiSet.empty st.hand

                let m = algorithm.findWord hand' st
                
                match m with
                | Some (points, move) -> 
                    debugPrint (sprintf "Player %d -> Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.
                    send cstream (SMPlay move)
                | None ->
                    if st.changeAllowed 
                    then
                        let tilesToChange = MultiSet.toList st.hand
                        send cstream (SMChange tilesToChange)
                    else send cstream SMPass
            else ()

            let msg = recv cstream

            match msg with
            | RCM (CMPlaySuccess(ms, points, newPieces)) ->
                (* Successful play by you. Update your state (remove old tiles, add the new ones, change turn, etc) *)
                let newPcs = List.fold (fun acc (x, k) -> MultiSet.add x k acc) MultiSet.empty newPieces
                let usedPcs = List.fold (fun acc (_, (id, (_))) -> MultiSet.addSingle id acc) MultiSet.empty ms
                let hand = MultiSet.sum (MultiSet.subtract st.hand usedPcs) newPcs
                
                // Add each tile from the move
                let tiles = List.fold (fun acc (coords,(_,tileVal)) -> Map.add coords tileVal acc) st.tiles ms

                (* New state *)
                let st' = State.mkState st.board st.dict st.players st.changeAllowed st.playerNumber st.numPlayers hand tiles (State.updPlayerTurn st)
                aux st'

            | RCM (CMChangeSuccess(newTiles)) ->
                (* No possible moves. Update your hand (remove old tiles, add the new ones, change turn) *)
                let newPcs = List.fold (fun acc (x, k) -> MultiSet.add x k acc) MultiSet.empty newTiles

                let st' = State.mkState st.board st.dict st.players st.changeAllowed st.playerNumber st.numPlayers newPcs st.tiles (State.updPlayerTurn st)
                aux st'
 
            | RCM (CMChange (pid, numTiles)) ->
                let st' = State.mkState st.board st.dict st.players st.changeAllowed st.playerNumber st.numPlayers st.hand st.tiles (State.updPlayerTurn st)
                aux st'

            | RCM (CMPlayed (pid, ms, points)) ->
                (* Successful play by other player. Update your state *)
                let tiles = List.fold (fun acc (coords,(_,tileVal)) -> Map.add coords tileVal acc) st.tiles ms

                let st' = State.mkState st.board st.dict st.players st.changeAllowed st.playerNumber st.numPlayers st.hand tiles (State.updPlayerTurn st)
                aux st'

            | RCM (CMPlayFailed (pid, ms)) ->
                let st' = State.mkState st.board st.dict st.players st.changeAllowed st.playerNumber st.numPlayers st.hand st.tiles (State.updPlayerTurn st)
                aux st'

            | RCM (CMPassed (pid)) ->
                let st' = State.mkState st.board st.dict st.players st.changeAllowed st.playerNumber st.numPlayers st.hand st.tiles (State.updPlayerTurn st)
                aux st'

            | RCM (CMForfeit (pid)) ->
                // Mark the player as not active
                let players = Map.add pid false st.players
                let st' = State.mkState st.board st.dict players st.changeAllowed st.playerNumber st.numPlayers st.hand st.tiles (State.updPlayerTurn st)
                aux st'

            | RCM (CMTimeout (pid)) ->
                let st' = State.mkState st.board st.dict st.players st.changeAllowed st.playerNumber st.numPlayers st.hand st.tiles (State.updPlayerTurn st)
                aux st'

            | RCM (CMGameOver _) -> ()

            | RGPE (_::GPENotEnoughPieces(changeTiles,availableTiles)::_) | RGPE (GPENotEnoughPieces(changeTiles,availableTiles)::_) ->
                let st' = State.mkState st.board st.dict st.players false st.playerNumber st.numPlayers st.hand st.tiles st.playerTurn
                aux st'
            
            | RGPE err -> printfn "Gameplay Error:\n%A" err; aux st


        aux st

    let startGame 
            (boardP : boardProg) 
            (dictf : bool -> Dictionary.Dict) 
            (numPlayers : uint32) 
            (playerNumber : uint32) 
            (playerTurn  : uint32)
            (hand : (uint32 * uint32) list)
            (tiles : Map<uint32, tile>)
            (timeout : uint32 option)
            (cstream : Stream) =
        debugPrint 
            (sprintf "Starting game!
                      number of players = %d
                      player id = %d
                      player turn = %d
                      hand =  %A
                      timeout = %A \n\n" numPlayers playerNumber playerTurn hand timeout)

        //let dict = dictf true // Uncomment if using a gaddag for your dictionary
        
        let dict = dictf false // Uncomment if using a trie for your dictionary
        
        let board = Parser.mkBoard boardP
                  
        let handSet = List.fold (fun acc (x, k) -> MultiSet.add x k acc) MultiSet.empty hand

        fun () -> playGame cstream tiles (State.mkState board dict (State.mkPlayersMap numPlayers) true playerNumber numPlayers handSet Map.empty playerTurn)
        