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
        tileLookup    : Map<uint32,tile>
        playerNumber  : uint32
        numPlayers    : uint32
        hand          : MultiSet.MultiSet<uint32>
        tiles         : Map<coord,idTile>
        playerTurn    : uint32
    }

    let mkState b d tileLU pn np h tiles pt = {
        board = b; 
        dict = d;  
        tileLookup = tileLU;
        playerNumber = pn; 
        numPlayers = np;
        hand = h; 
        tiles = tiles;
        playerTurn = pt;
    }

    let board st         = st.board
    let dict st          = st.dict
    let tileLookup st    = st.tileLookup
    let playerNumber st  = st.playerNumber
    let numPlayers st    = st.numPlayers
    let hand st          = st.hand
    let playerTurn st    = st.playerTurn
    

    (* Must be able to handle forfeits if multiplayer is implemented *)
    let updPlayerTurn st =
        let t = playerTurn st + 1u
        if t > numPlayers st then 1u
        else t

    // If square is free returns None, if taken returns Some (square, tile)
    let checkSquareFree coords st = st.board.squares coords |> fun (StateMonad.Success sqr) -> sqr |>
        function
        | Some sqr -> Map.tryFind coords st.tiles |> Option.map (fun tile -> (sqr,tile))
        | None -> None
        
    // let checkDirection <- maybe we can try make a word and then check is it possible to put it?
    // or maybe it's easier to just check everytime we want put more letters 
    
    // just check is this word exist or not
    let checkWord word = Dictionary.lookup word

    let tileByID id (st: state) = Map.tryFind id st.tileLookup

    let handToTiles hand st =
        MultiSet.fold (fun acc id count -> 
            match tileByID id st with
            | Some t -> MultiSet.add (id,t.MinimumElement) count acc
            | None -> acc
            ) MultiSet.empty hand
    

module internal algorithm =
    

    type Direction =
        | Right = 0
        | Down = 1

    let checkSquareSideBefore (x,y) dir st =
        match dir with
        | Direction.Right -> State.checkSquareFree (x,y-1) st
        | Direction.Down -> State.checkSquareFree (x-1,y) st

    let checkSquareSideAfter (x,y) dir st =
        match dir with
        | Direction.Right -> State.checkSquareFree (x,y+1) st
        | Direction.Down -> State.checkSquareFree (x+1,y) st

    let shouldUseSquare coords dir st =
        match checkSquareSideBefore coords dir st with
        | Some _ -> false
        | None -> 
            match checkSquareSideAfter coords dir st with
            | Some _ -> false
            | None -> true


    let rec tryNextLetter (x,y) dir dict hand acc st =
        match State.checkSquareFree (x,y) st with
        | Some (_, (id,(c,v))) -> 
            match Dictionary.step c dict with
            | Some (_, dict') -> 
                let acc' = ((x,y),(id,(c,v)))::acc
                if dir = Direction.Right then tryNextLetter (x+1,y) dir dict' hand acc' st
                else tryNextLetter (x,y+1) dir dict' hand acc' st
            | None -> None
        | None -> 
            if shouldUseSquare (x,y) dir st 
            then checkEach (x,y) dir dict hand hand acc st
            else None
    and checkEach coords dir dict hand untried acc st = 
        // If all tiles on hand have been tried, return None
        if MultiSet.isEmpty untried then None 
        else
            let tile = (MultiSet.toList untried).Head
            let c = tile |> fun (_,(c,_)) -> c
            // Check if letter is usable in dictionary
            match Dictionary.step c dict with
            | Some (b, dict') -> 
                // If word is complete, return accumulator
                if b then Some ((coords,tile)::acc)
                else 
                    let acc' = (coords,tile)::acc
                    tryNextLetter coords dir dict' (MultiSet.removeSingle tile hand) acc' st
            | None ->
                // If letter is not usable, check next tile in hand
                checkEach coords dir dict hand (MultiSet.removeSingle tile untried) acc st

        
            
    // Try to create a word starting from given tile
    // If no word is found horizontally, tries vertically
    let wordFromTile (coords,tile) dict hand st =
        let acc = [(coords, tile)]
        let result = match checkSquareSideBefore coords Direction.Right st with
                     | Some _ -> None
                     | None -> tryNextLetter coords Direction.Right dict hand acc st
        match result with
        | Some acc -> Some acc
        | None -> 
            match checkSquareSideBefore coords Direction.Down st with
            | Some _ -> None
            | None -> tryNextLetter coords Direction.Down dict hand acc st


    let rec findFirstWord coords dict hand acc st =
        match checkEachFW coords dict hand hand acc st with
        | Some acc' -> Some acc'
        | None -> None
    and checkEachFW (x,y) dict hand untried acc st = 
           if MultiSet.isEmpty untried then None 
           else
               let tile = (MultiSet.toList untried).Head
               let c = tile |> fun (_,(c,_)) -> c
               match Dictionary.step c dict with
               | Some (b, dict') -> 
                   if b then Some (((x,y),tile)::acc)
                   else 
                       let acc' = ((x,y),tile)::acc
                       findFirstWord (x,y+1) dict' (MultiSet.removeSingle tile hand) acc' st
               | None ->
                   checkEachFW (x,y) dict hand (MultiSet.removeSingle tile untried) acc st



module Scrabble =
    open System.Threading

    let playGame cstream pieces (st : State.state) =

        let rec aux (st : State.state) =
            Print.printHand pieces (State.hand st)

            // remove the force print when you move on from manual input (or when you have learnt the format)
            if st.playerTurn = st.playerNumber then
                // forcePrint "Input move (format '(<x-coordinate> <y-coordinate>
                // <piece id><character><point-value> )*', note the absence of space between the last inputs)\n\n"
                
                //let input =  System.Console.ReadLine()
                //let move = RegEx.parseMove input
                let hand' = State.handToTiles st.hand st
                if st.tiles.IsEmpty 
                then 
                    match algorithm.findFirstWord (0,0) st.dict hand' [] st with
                    | Some move -> 
                        debugPrint (sprintf "Player %d -> Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.
                        send cstream (SMPlay move)
                    | None -> 
                        send cstream SMPass
                else 
                    let l = Map.toList st.tiles
                    let rec tryTile (untried: (coord*State.idTile) list) =
                        match algorithm.wordFromTile untried.Head st.dict hand' st with
                        | Some move -> 
                            debugPrint (sprintf "Player %d -> Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.
                            send cstream (SMPlay move)
                        | None -> 
                            if List.isEmpty untried then send cstream SMPass
                            else tryTile untried.Tail
                    tryTile l
                
                
            else ()

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
                let st' = State.mkState st.board st.dict st.tileLookup st.playerNumber st.numPlayers hand tiles (State.updPlayerTurn st)
                aux st'

            | RCM (CMPlayed (pid, ms, points)) ->
                (* Successful play by other player. Update your state *)

                (* New state *)
                let st' = State.mkState st.board st.dict st.tileLookup st.playerNumber st.numPlayers st.hand st.tiles (State.updPlayerTurn st)
                aux st'

            | RCM (CMPlayFailed (pid, ms)) ->
                (* Failed play. Update your state *)
                let st' = State.mkState st.board st.dict st.tileLookup st.playerNumber st.numPlayers st.hand st.tiles (State.updPlayerTurn st)
                aux st'

            | RCM (CMGameOver _) -> ()
            | RCM a -> failwith (sprintf "not implmented: %A" a)
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

        fun () -> playGame cstream tiles (State.mkState board dict tiles playerNumber numPlayers handSet Map.empty playerTurn)
        