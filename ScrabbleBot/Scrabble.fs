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
    type idTile = (uint32 * (char * int))

    let tileVal ((_,(_,v)):idTile) = v
    let tileId ((id,_):idTile) = id
    

    type state = {
        board         : Parser.board
        dict          : ScrabbleUtil.Dictionary.Dict
        playerNumber  : uint32
        numPlayers    : uint32
        hand          : MultiSet.MultiSet<uint32>
        tiles         : Map<coord,idTile>
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

    let getSquare coords st = st.board.squares coords |> function 
                                                         | StateMonad.Success sqr -> sqr
                                                         | _ -> None

    let checkSquareValid coords st =  st.board.squares coords |> function 
        | StateMonad.Success _ -> true
        | StateMonad.Failure _ -> false

    // If square is free returns None, if taken returns Some (square, tile)
    let checkSquareFree coords st = 
        st.board.squares coords |> 
        fun (StateMonad.Success sqr) -> sqr |> function
                                               | Some sqr -> Map.tryFind coords st.tiles |> Option.map (fun tile -> (sqr,tile))
                                               | None -> None
        
    // let checkDirection <- maybe we can try make a word and then check is it possible to put it?
    // or maybe it's easier to just check everytime we want put more letters 
    
    // just check is this word exist or not
    let checkWord word = Dictionary.lookup (List.fold (fun acc (c,v) -> acc + c.ToString()) "" word)


module internal algorithm =
    
    let tileChar = fun (_,(c,_)) -> c
    let tilePoints = fun (_,(_,p)) -> p
    let tileVal = fun (_,t) -> t

    // Functions to update coordinates
    let right = fun (x,y) -> (x+1,y)
    let left = fun (x,y) -> (x-1,y)
    let up = fun (x,y) -> (x,y-1)
    let down = fun (x,y) -> (x,y+1)

    // Calculate the points in the complete word from the squareFuns
    let calcPoints word sqrs = 
        let f = List.sortBy (fun (_,(k,_)) -> k) (Map.toList sqrs)
        List.fold (fun acc (pos,(_,sf)) -> 
            match acc with
            | StateMonad.Success acc -> sf word pos acc
            | _ -> sf word pos 0) (StateMonad.Success 0) f

    // Add squareFun from a given square to the map of squareFuns
    let addSF pos (sqr:Parser.square) sqrs = Map.fold (fun acc k v -> Map.add pos (k,v) acc) sqrs sqr

    

    let findWord tiles dict hand st =

        // Check squares to left and right
        let shouldUseCheckH = fun coords -> 
            (State.checkSquareFree (left coords) st).IsNone && (State.checkSquareFree (right coords) st).IsNone
        // Check squares above and below
        let shouldUseCheckV = fun coords -> 
            (State.checkSquareFree (up coords) st).IsNone && (State.checkSquareFree (down coords) st).IsNone

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
            *)
            let rec tryNextLetter coords dict hand pos word move sqrs  =
                let sqrOption = State.getSquare coords st
                let sqr = sqrOption |> fun (Some sqr) -> sqr
                
                if State.checkSquareValid coords st then
                    match State.checkSquareFree coords st with
                    | Some (_, (id,(c,v))) -> 
                        match Dictionary.step c dict with
                        // Adds the existing tile to the word and the sqrs, but not to the move
                        | Some (_, dict') -> tryNextLetter (next coords) dict' hand (pos+1) (word@[(c,v)]) move (addSF pos sqr sqrs)
                        | None -> None
                    | None -> 
                        // Checks if the square exists on the board before trying any tiles
                        if not (MultiSet.isEmpty hand) && sqrOption.IsSome && sidesCheck coords
                        then 
                            MultiSet.fold (fun mv tile n -> 
                                match Dictionary.step (tileChar tile) dict with
                                | Some (b,dict') -> 
                                    match tryNextLetter (next coords) dict' (MultiSet.removeSingle tile hand) (pos+1) (word@[tileVal tile]) ((coords,tile)::move) (addSF pos sqr sqrs) with
                                    | Some (points,move) -> 
                                        match mv with
                                        | Some (points',_) -> if points > points' then Some (points,move) else mv
                                        | None -> Some (points,move)
                                    | None -> 
                                        let getPoints = calcPoints (word@[tileVal tile]) (addSF pos sqr sqrs) |> function 
                                                                                                              | StateMonad.Success i -> i
                                                                                                              | _ -> 0
                                        // Rechecks if word is in dictionary before returning it.
                                        // If the square after the last letter is not free, don't use the move.
                                        if b && State.checkWord word st.dict && (State.checkSquareFree (next coords) st).IsNone 
                                        then Some (getPoints, ((coords,tile)::move)) 
                                        else mv
                                | None -> mv
                                ) None hand
                        else None
                else None

            tryNextLetter (next coords) dict hand 1 word [] (addSF 0 (State.getSquare coords st |> fun (Some sqr) -> sqr) Map.empty)


                
        // Start finding a word from a given tile, compare best word horizontally and vertically to return the best
        // First try horizontal, then try vertical
        let startWord (coords,tile) dict =
            // Check if square before is free before starting word
            let tryRight dict' = 
                if State.checkSquareValid coords st && (State.checkSquareFree (left coords) st).IsNone 
                then tryDirection coords right shouldUseCheckV dict' [tileVal tile]
                else None
            let tryDown dict' = 
                if State.checkSquareValid coords st && (State.checkSquareFree (up coords) st).IsNone 
                then tryDirection coords down shouldUseCheckH dict' [tileVal tile]
                else None

            match Dictionary.step (tileChar tile) dict with
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



    // Finds a word only from the hand
    let rec findFirstWord coords dict hand pos word move sqrs st =
        let sqrOption = State.getSquare coords st
        let sqr = sqrOption |> fun (Some sqr) -> sqr

        // Checks if square exists before trying letters
        if MultiSet.isEmpty hand || sqrOption.IsNone then None
        else
            MultiSet.fold (fun mv tile n ->
                match Dictionary.step (tileChar tile) dict with
                | Some (b,dict') -> 
                    match findFirstWord (down coords) dict' (MultiSet.removeSingle tile hand) (pos+1) (word@[tileVal tile]) ((coords,tile)::move) (addSF pos sqr sqrs) st with
                    | Some (points,move) -> 
                        match mv with
                        | Some (points',_) -> if points > points' then Some (points,move) else mv
                        | None -> Some (points,move)
                    | None -> if b then Some (calcPoints (word@[tileVal tile]) (addSF pos sqr sqrs) |> function 
                                                                                                       | StateMonad.Success i -> i
                                                                                                       | _ -> 0
                                                                                                       , ((coords,tile)::move)) else mv
                | None -> mv
            ) None hand



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
                            | Some (t: tile) -> MultiSet.add (id, t.MinimumElement) count acc
                            | None -> acc
                            ) MultiSet.empty st.hand

            let m = match Map.isEmpty st.tiles with
                    | true -> algorithm.findFirstWord (st.board.center) st.dict hand' 0 [] [] Map.empty st
                    | false -> algorithm.findWord st.tiles st.dict hand' st
                
            //else ()
            match m with
            | Some (points, move) -> 
                debugPrint (sprintf "Player %d -> Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.
                send cstream (SMPlay move)
            | None ->
                let tailsToChange = MultiSet.toList st.hand
                send cstream (SMChange tailsToChange)


            let msg = recv cstream
            //debugPrint (sprintf "Player %d <- Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.

            match msg with
            | RCM (CMPlaySuccess(ms, points, newPieces)) ->
                
                (* Successful play by you. Update your state (remove old tiles, add the new ones, change turn, etc) *)
                let newPcs = List.fold (fun acc (x, k) -> MultiSet.add x k acc) MultiSet.empty newPieces
                let usedPcs = List.fold (fun acc (_, (id, (_))) -> MultiSet.addSingle id acc) MultiSet.empty ms
                let hand = MultiSet.sum (MultiSet.subtract st.hand usedPcs) newPcs
                
                // Add each tile from the move
                let tiles = List.fold (fun acc (coords,tile) -> Map.add coords tile acc) st.tiles ms

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
        