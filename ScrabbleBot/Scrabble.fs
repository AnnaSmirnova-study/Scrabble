namespace ScrabbleFighter

open System.Linq
open ScrabbleUtil
open ScrabbleUtil.ServerCommunication

open System.IO

open ScrabbleUtil.DebugPrint

// The RegEx module is only used to parse human input. It is not used for the final product.

module RegEx =
    open System.Text.RegularExpressions

    let (|Regex|_|) pattern input =
        let m = Regex.Match(input, pattern)
        if m.Success then Some(List.tail [ for g in m.Groups -> g.Value ])
        else None

    let parseMove ts =
        let pattern = @"([-]?[0-9]+[ ])([-]?[0-9]+[ ])([0-9]+)([A-Z]{1})([0-9]+)[ ]?" 
        Regex.Matches(ts, pattern) |>
        Seq.cast<Match> |> 
        Seq.map 
            (fun t -> 
                match t.Value with
                | Regex pattern [x; y; id; c; p] ->
                    ((x |> int, y |> int), (id |> uint32, (c |> char, p |> int)))
                | _ -> failwith "Failed (should never happen)") |>
        Seq.toList

module Print =
    let printHand pieces hand =
        hand |>
        MultiSet.fold (fun _ x i -> forcePrint (sprintf "%d -> (%A, %d)\n" x (Map.find x pieces) i)) ()

module State = 
    // Make sure to keep your state localised in this module. It makes your life a whole lot easier.
    // Currently, it only keeps track of your hand, your player numer, your board, and your dictionary,
    // but it could, potentially, keep track of other useful
    // information, such as number of players, player turn, etc.

    // Maybe move this somewhere else
    //type idTile = (uint32 * (char * int))
    type tileVal = (char * int)

    //let tileVal ((_,(_,v)):idTile) = v
    //let tileId ((id,_):idTile) = id
    

    type state = {
        board         : Parser.board
        dict          : ScrabbleUtil.Dictionary.Dict
        playerNumber  : uint32
        numPlayers    : uint32
        hand          : MultiSet.MultiSet<uint32>
        tiles         : Map<coord,tileVal>
        playerTurn    : uint32
    }

    let mkState b d pn np h tiles pt = {
        board = b; 
        dict = d;  
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
    

    (* Must be able to handle forfeits if multiplayer is implemented *)
    let updPlayerTurn st =
        let t = playerTurn st + 1u
        if t > numPlayers st then 1u
        else t

    // If square is free returns Some (Some square, None)
    // If taken returns Some (Some square, Some tile)
    // Any other result means the square is invalid and cannot be used
    let checkSquareTile coords st = st.board.squares coords |> function 
        | StateMonad.Success sqr -> sqr |> Option.map (fun sqr -> sqr) |> fun sqr -> Some (sqr, Map.tryFind coords st.tiles)
        | StateMonad.Failure _ -> None
        
    // let checkDirection <- maybe we can try make a word and then check is it possible to put it?
    // or maybe it's easier to just check everytime we want put more letters 
    
    // just check is this word exist or not
    let checkWord word = Dictionary.lookup (List.fold (fun acc (c,v) -> acc + c.ToString()) "" word)


module internal algorithm =

    type crossFun = char*int -> ((char*int)*Parser.square) list

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
    //let idTilePoints = fun (_,(_,p)) -> p
    //let idTileVal = fun (_,t) -> t

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


    // Add squareFun from a given square to the map of squareFuns
    let addSF pos (sqr:Parser.square) sqrs = Map.fold (fun acc k v -> Map.add pos (k,v) acc) sqrs sqr

    (*
    let tryEndWord b coords word sqrs move st def = 
        match State.checkSquareTile coords st with
        | Some (Some _, Some _) -> def
        | _ -> if b && (List.isEmpty move) then Some (calcPoints (List.rev word) sqrs, move) else def

        
    let findWord tiles dict hand st =

        (*
            Try finding a word in the given direction.
            next is the function for updating the coordinates
            sidesCheck is the function for checking the squares next to the coordinates
        *)
        let tryDirection coords next sidesCheck dict word =
            (*
                Recursive function to try next letter in the word.
                Uses fold on the hand to try each letter.

                -- Used for points calculation
                pos is the char position in the word.
                word is the list of tiles in the word.
                sqrs is a map with the squareFuns according to the pos.

                valid is true if the word contains at least one new tile
            *)
            let rec tryNextLetter coords dict hand pos word move sqrs valid  =
                match State.checkSquareTile coords st with
                | Some (Some sqr, Some (c,v)) -> 
                    match Dictionary.step c dict with
                    // Adds the existing tile to the word and the sqrs, but not to the move
                    | Some (b, dict') -> 
                        match tryNextLetter (next coords) dict' hand (pos+1) ((c,v)::word) move (addSF pos sqr sqrs) valid with
                        //Option.defaultValue (tryEndWord b (next coords) ((c,v)::word) (addSF pos sqr sqrs) move st None) |> 
                        | Some move' -> Some move'
                        | None -> tryEndWord b (next coords) ((c,v)::word) (addSF pos sqr sqrs) move st None
                    | _ -> None
                | Some (Some sqr, None) -> 
                    if not (MultiSet.isEmpty hand) && sidesCheck coords
                    then 
                        MultiSet.fold (fun mv (id,tile) _ -> 
                            Set.fold (fun mv' tileVal ->
                                match Dictionary.step (tileChar tileVal) dict with
                                | Some (b,dict') -> 
                                    match tryNextLetter (next coords) dict' (MultiSet.removeSingle (id,tile) hand) (pos+1) (tileVal::word) ((coords,(id,tileVal))::move) (addSF pos sqr sqrs) true with
                                    | Some (points,move) -> 
                                        match mv' with
                                        | Some (points',_) -> if points > points' then Some (points,move) else mv'
                                        | None -> Some (points,move)
                                    | None -> 
                                        // Rechecks if word is in dictionary before returning it.
                                        // If the square after the last letter is not free, don't use the move.
                                        match State.checkSquareTile (next coords) st with
                                        | Some (Some sqr, None) when b && valid -> Some (calcPoints (List.rev (tileVal::word)) (addSF pos sqr sqrs), ((coords,(id,tileVal))::move))
                                        | _ -> mv'
                                | None -> mv'
                            ) mv tile
                        ) None hand
                    else None
                | _ -> None

            match State.checkSquareTile coords st with
            | Some (Some sqr, _) -> tryNextLetter (next coords) dict hand 1 word [] (addSF 0 sqr Map.empty) false
            | _ -> None


        // Check squares to to the sides of a coordinate
        let checkSides before after = fun coords -> 
            match State.checkSquareTile (before coords) st with
            | Some (Some _, None) -> 
                match State.checkSquareTile (after coords) st with
                | Some (Some _, None) -> true
                | _ -> false
            | _ -> false

        

        (*
        let checkCrossingFun before after squares sqr coords : crossFun option =
            let rec getNext coords' next acc =
                match checkSquareTile coords' squares with
                | Some (Some sqr, Some tile) -> getNext (next coords) next ((tile,sqr)::acc)
                | _ -> acc
            let getBefore = getNext (before coords) before []
            let getAfter = getNext (after coords) after [] |> List.rev
            match (getBefore,getAfter) with
            | ([],[]) -> None
            | (before,after) -> Some (fun tile -> (before@((tile,sqr)::after)))

            let rec checkBefore coords' next =
                match checkSquareTile coords' squares with
                | Some (Some sqr, Some tile) -> 
                    match checkBefore (next coords) next with
                    | Some (pos, word, sqrs) -> Some (pos+1, tile::word, addSF (pos+1) sqr sqrs)
                    | None -> (0, [tile], addSF 0 sqr Map.empty)
                | _ -> None
            let rec checkAfter coords' next (pos,word,sqrs) =
                match checkSquareTile coords' squares with
                | Some (Some sqr, Some tile) -> checkAfter (next coords') next (pos+1, tile::word, addSF (pos+1) sqr sqrs)
                | _ -> (pos,word,sqrs)
            let getBefore = checkBefore (before coords) before
            let getAfter = checkAfter (after coords) after 
            *)

        

                
        // Start finding a word from a given tile, compare best word horizontally and vertically to return the best
        // First try horizontal, then try vertical
        let startWord (coords,tileVal) dict =
            // Check if square before is free before starting word
            let tryRight dict' = 
                match State.checkSquareTile (left coords) st with
                | Some (Some sqr, None) -> tryDirection coords right (checkSides up down) dict' [tileVal]
                | _ -> None

            let tryDown dict' = 
                match State.checkSquareTile (up coords) st with
                | Some (Some sqr, None) -> tryDirection coords down (checkSides left right) dict' [tileVal]
                | _ -> None

            match Dictionary.step (tileChar tileVal) dict with
                    | Some (_, dict') -> 
                        match tryRight dict' with
                        | Some (points,move) -> 
                            match tryDown dict' with
                            | Some (points',move') -> if points > points' then Some (points,move) else Some (points',move')
                            | None -> Some (points,move)
                        | None -> tryDown dict'
                    | None -> None



        // For each tile on the board, find the move with the highest points and compare to return the best
        if Map.isEmpty tiles then None
        else 
            Map.fold (fun mv coords tile ->
                match startWord (coords,tile) dict with
                | Some (points,move) -> 
                    match mv with
                    | Some (points',_) -> if points > points' then Some (points,move) else mv
                    | None -> Some (points,move)
                | None -> mv
            ) None tiles
            *)


    let findWord hand (st:State.state) =
        let greatest a b =
            match a with
            | Some (p,m) -> 
                match b with
                | Some (p',m') -> if p > p' then Some (p,m) else Some (p',m')
                | None -> Some (p,m)
            | None -> b

        let calcPoints word sqrs = 
            let f = List.sortBy (fun (_,(k,_)) -> k) (Map.toList sqrs)
            List.fold (fun acc (pos,(_,sf)) -> 
                match sf word pos acc with
                | StateMonad.Success acc' -> acc'
                | _ -> acc) 0 f

        
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
            
        // Try to start a word from each square in the list (which was made in getSquares)
        let rec tryFromNextSquare squares dict hand =
            match squares with
            | (ws,Some tileVal)::tail when ws.pos < 1 -> 
                match Dictionary.step (tileChar tileVal) dict with
                | Some (b,dictStep) -> tryNextLetter tail dictStep hand 1 [tileVal] (addSF 0 ws.sqr Map.empty) []
                | None -> tryFromNextSquare tail dict hand
            | (ws,None)::tail when ws.pos < 1 -> 
                MultiSet.fold (fun mv (id,tile) _ -> 
                    Set.fold (fun mv' tileVal ->
                        match Dictionary.step (tileChar tileVal) dict with
                        | Some (_,dictStep) -> 
                            match tryNextLetter tail dictStep (MultiSet.removeSingle (id,tile) hand) 1 [tileVal] (addSF 0 ws.sqr Map.empty) [(ws.coords,(id,tileVal))] with
                            | Some (points,move) -> 
                                match mv' with
                                | Some (points',_) -> if points > points' then Some (points,move) else mv'
                                | None -> Some (points,move)
                            | None -> mv'
                        | None -> mv'
                    ) mv tile
                ) None hand
            | _ -> None
    
        // Check if a square is free
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

        // Get a list of the squares a word can be placed on in a given direction
        // To prevent checking the same squares over and over
        let getSquares boardSquares count back forward sidesFree coords  =
            // If the next square is not free, the word cannot end here
            let canEnd coords' = 
                match checkSquareTile (forward coords') boardSquares with
                | Some (Some _, Some _) -> false
                | _ -> true

            let rec getSquaresAfter coords' next' count' pos acc = 
                match checkSquareTile coords' boardSquares with
                | Some (Some sqr, None) -> if (count' >= 0u) && (sidesFree coords') then getSquaresAfter (next' coords') next' (count'-1u) (pos+1) (((mkWS coords' sqr pos (canEnd coords')),None)::acc) else acc
                | Some (Some sqr, Some tile) -> getSquaresAfter (next' coords') next' count' (pos+1) (((mkWS coords' sqr pos (canEnd coords')),Some tile)::acc)
                | _ -> acc
            let rec getSquaresBefore coords' next' count' pos acc =
                match checkSquareTile coords' boardSquares with
                | Some(Some sqr, None) -> if (count' > 3u) && (sidesFree coords') then getSquaresBefore (next' coords') next' (count'-1u) (pos-1) (((mkWS coords' sqr pos false),None)::acc) else acc
                | _ -> acc.Tail
            List.rev (getSquaresAfter coords forward count 0 []) |> getSquaresBefore (back coords) back count -1


        //let findWord hand (st:State.state) = 
        let sidesFreeH = sidesFree st.board.squares up down
        let sidesFreeV = sidesFree st.board.squares left right

        let squaresH = getSquares st.board.squares (MultiSet.size hand) left right sidesFreeH
        let squaresV = getSquares st.board.squares (MultiSet.size hand) up down sidesFreeV

        let tryH coords = 
            match checkSquareTile (left coords) st.board.squares with 
            | Some (Some _, Some _) -> None
            | _ -> tryFromNextSquare (squaresH coords) st.dict hand 
        let tryV coords =
            match checkSquareTile (up coords) st.board.squares with 
            | Some (Some _, Some _) -> None
            | _ -> tryFromNextSquare (squaresV coords) st.dict hand 

        if Map.isEmpty st.tiles then tryV st.board.center//greatest (tryH st.board.center) (tryV st.board.center)
        else
            Map.fold (fun mv coords _ ->
                greatest (tryH coords) (tryV coords) |> greatest mv
            ) None st.tiles




    (*
    // Finds a word only from the hand
    let rec findFirstWord coords dict hand pos word move sqrs st =
        // Checks if square exists before trying letters
        match State.checkSquareTile coords st with
        | Some (Some sqr, _) when not (MultiSet.isEmpty hand) -> 
            MultiSet.fold (fun mv (id,tile) _ ->
                Set.fold (fun mv' tileVal ->
                    match Dictionary.step (tileChar tileVal) dict with
                    | Some (b,dict') -> 
                        match findFirstWord (down coords) dict' (MultiSet.removeSingle (id,tile) hand) (pos+1) (word@[tileVal]) ((coords,(id,tileVal))::move) (addSF pos sqr sqrs) st with
                        | Some (points,move) -> 
                            match mv with
                            | Some (points',_) -> if points > points' then Some (points,move) else mv
                            | None -> Some (points,move)
                        | None -> if b then Some (calcPoints (List.rev (tileVal::word)) (addSF pos sqr sqrs), ((coords,(id,tileVal))::move)) else mv
                    | None -> mv'
                ) mv tile
            ) None hand
        | _ -> None
        *)



module Scrabble =
    open System.Threading

    let playGame cstream pieces (st : State.state) =
            

        let rec aux (st : State.state) =
            Print.printHand pieces (State.hand st)

            // remove the force print when you move on from manual input (or when you have learnt the format)
            //if st.playerTurn = st.playerNumber then
                // forcePrint "Input move (format '(<x-coordinate> <y-coordinate>
                // <piece id><character><point-value> )*', note the absence of space between the last inputs)\n\n"
                
            // Waits for input before startung turn (just press enter)
            let input =  System.Console.ReadLine()
                //let move = RegEx.parseMove input

            // All wildcard tiles are treated as 'A'
            let hand' = MultiSet.fold (fun acc id count -> 
                            match Map.tryFind id pieces with
                            | Some (t: tile) -> MultiSet.add (id, t) count acc
                            | None -> acc
                            ) MultiSet.empty st.hand

                            
            //let m = match Map.isEmpty st.tiles with
            //        | true -> algorithm.findFirstWord (st.board.center) st.dict hand' 0 [] [] Map.empty st
            //        | false -> algorithm.findWord hand' st
            

            let m = algorithm.findWord hand' st
                
            //else ()
            match m with
            | Some (points, move) -> 
                debugPrint (sprintf "Player %d -> Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.
                send cstream (SMPlay move)
            | None ->
                let tilesToChange = MultiSet.toList st.hand
                send cstream (SMChange tilesToChange)


            let msg = recv cstream
            //debugPrint (sprintf "Player %d <- Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.

            match msg with
            | RCM (CMPlaySuccess(ms, points, newPieces)) ->
                
                (* Successful play by you. Update your state (remove old tiles, add the new ones, change turn, etc) *)
                let newPcs = List.fold (fun acc (x, k) -> MultiSet.add x k acc) MultiSet.empty newPieces
                let usedPcs = List.fold (fun acc (_, (id, (_))) -> MultiSet.addSingle id acc) MultiSet.empty ms
                let hand = MultiSet.sum (MultiSet.subtract st.hand usedPcs) newPcs
                
                // Add each tile from the move
                let tiles = List.fold (fun acc (coords,(_,tileVal)) -> Map.add coords tileVal acc) st.tiles ms

                (* New state *)
                let st' = State.mkState st.board st.dict st.playerNumber st.numPlayers hand tiles (State.updPlayerTurn st)
                aux st'

            | RCM (CMChangeSuccess(newTiles)) ->
                
                (* No possible moves. Update your hand (remove old tiles, add the new ones, change turn) *)
                let newPcs = List.fold (fun acc (x, k) -> MultiSet.add x k acc) MultiSet.empty newTiles
                let hand = newPcs

                let st' = State.mkState st.board st.dict st.playerNumber st.numPlayers hand st.tiles (State.updPlayerTurn st)
                aux st'
 
                
            | RCM (CMPlayed (pid, ms, points)) ->
                (* Successful play by other player. Update your state *)

                (* New state *)
                // change turn, add tiles, don't need to use points
                let st' = State.mkState st.board st.dict st.playerNumber st.numPlayers st.hand st.tiles (State.updPlayerTurn st)
                aux st'

            | RCM (CMPlayFailed (pid, ms)) ->
                (* Failed play. Update your state *)
                
                // change turn 
                let st' = State.mkState st.board st.dict st.playerNumber st.numPlayers st.hand st.tiles (State.updPlayerTurn st)
                aux st'

            | RCM (CMPassed (pid)) ->
                
                // change turn
                let st' = State.mkState st.board st.dict st.playerNumber st.numPlayers st.hand st.tiles (State.updPlayerTurn st)
                aux st'

            | RCM (CMGameOver _) -> ()
            | RCM a -> failwith (sprintf "not implmented: %A" a)
            
            | RGPE err -> printfn "Gameplay Error:\n%A" err; aux st // make a flag to make less tiles from hand


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

        fun () -> playGame cstream tiles (State.mkState board dict playerNumber numPlayers handSet Map.empty playerTurn)
        