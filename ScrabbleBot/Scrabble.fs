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
    
    
    // We make new type to keep it right for sending move to server
    type idTile = (uint32 * (char * int))
    let tileVal ((_,(_,v)):idTile) = v
    let tileId ((id,_):idTile) = id
    

    type state = {
        board         : Parser.board
        dict          : ScrabbleUtil.Dictionary.Dict
        tileLookup    : Map<uint32, tile>
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
    
    // just check is this word exist or not
    let checkWord word = Dictionary.lookup word

    // Find tail by it's ID
    let tileByID id (st: state) = Map.tryFind id st.tileLookup

    // Turn hand from Multiset<uint32> to useful 
    let handToTiles hand st =
        MultiSet.fold (fun acc id count -> 
            match tileByID id st with
            | Some t -> MultiSet.add (id, t.MinimumElement) count acc
            | None -> acc
            ) MultiSet.empty hand
    

module internal algorithm =
    
    // What way we will go
    type Direction =
        | Right = 0
        | Down = 1

    // If we go Down we check square on left side of considered square, if Right - above 
    let checkSquareSideBefore (x, y) dir st =
        match dir with
        | Direction.Right -> State.checkSquareFree (x, y-1) st
        | Direction.Down -> State.checkSquareFree (x-1, y) st

    // If we go Down we check square on right side of considered square, if Right - under
    let checkSquareSideAfter (x,y) dir st =
        match dir with
        | Direction.Right -> State.checkSquareFree (x, y+1) st
        | Direction.Down -> State.checkSquareFree (x+1, y) st

    // Connect two previous functions and check side squares of considered square
    // Here we have true if everything is free and we can put letter to considered square, and false otherwise
    let shouldUseSquare coords dir st =
        match checkSquareSideBefore coords dir st with
        | Some _ -> false
        | None -> 
            match checkSquareSideAfter coords dir st with
            | Some _ -> false
            | None -> true

    // We have coordinates of considered square and want to find next letter in word
    let rec tryNextLetter (x, y) dir dict hand acc st =
        // First we check is this square free
        match State.checkSquareFree (x, y) st with
        // if it's not and we have tail there
        | Some (_, (id,(c, v))) ->
            // Look is this letter a beginning of any word in dict
            match Dictionary.step c dict with
            | Some (_, dict') ->
                // If yes, we call function again with new dict and coord, depends on our direction 
                if dir = Direction.Right then tryNextLetter (x+1, y) dir dict' hand acc st
                else tryNextLetter (x, y+1) dir dict' hand acc st
            // if it's not a word, we won't continue
            | None -> None
        // If square is free
        | None ->
            // We check squares around, to be sure we can make move
            if shouldUseSquare (x, y) dir st
            // Then try every letter from our hand
            then checkEach (x, y) dir dict hand hand acc st
            else None
    // Here we try to play by every letter from hand
    and checkEach (x, y) dir dict hand untried acc st = 
        // If all tiles on hand have been tried, return None
        if MultiSet.isEmpty untried then None 
        else
            // We keep first tail from unused 
            let tile = (MultiSet.toList untried).Head
            let c = tile |> fun (_,(c,_)) -> c // Keep only value
            // Check if letter is usable in dictionary
            match Dictionary.step c dict with
            | Some (b, dict') -> 
                // If word is complete, return accumulator with final tail
                if b then Some (((x,y),tile)::acc)
                else
                    // If it's not complete but word it's still possible put it in acc and continue
                    let acc' = ((x,y),tile)::acc
                    match dir with
                    | Direction.Right -> tryNextLetter (x+1, y) dir dict' (MultiSet.removeSingle tile hand) acc' st
                    | Direction.Down -> tryNextLetter (x, y+1) dir dict' (MultiSet.removeSingle tile hand) acc' st
            | None ->
                // If letter is not usable, check next tile in hand
                checkEach (x,y) dir dict hand (MultiSet.removeSingle tile untried) acc st
  
            
    // Try to create a word starting from given tile
    // If no word is found horizontally, tries vertically
    let wordFromTile ((x,y),tile) dict hand st =
        let acc = []
        let c = tile |> fun (_,(c,_)) -> c
        match Dictionary.step c dict with
        | Some (_, dict') -> 
            let result = match checkSquareSideBefore (x,y) Direction.Right st with
                         | Some _ -> None
                         | None -> tryNextLetter (x+1,y) Direction.Right dict' hand acc st
            match result with
            | Some acc -> Some acc
            | None -> 
                match checkSquareSideBefore (x,y) Direction.Down st with
                | Some _ -> None
                | None -> tryNextLetter (x,y+1) Direction.Down dict' hand acc st
        | None -> None


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
            //if st.playerTurn = st.playerNumber then
                // forcePrint "Input move (format '(<x-coordinate> <y-coordinate>
                // <piece id><character><point-value> )*', note the absence of space between the last inputs)\n\n"
                
                //let input =  System.Console.ReadLine()
                //let move = RegEx.parseMove input
            let hand' = State.handToTiles st.hand st
            let m = match Map.isEmpty st.tiles with
                    | true -> algorithm.findFirstWord (0,0) st.dict hand' [] st
                    | false -> 
                        let l = Map.toList st.tiles
                        let rec tryTile (untried: (coord*State.idTile) list) =
                            match algorithm.wordFromTile untried.Head st.dict hand' st with
                            | Some move -> Some move
                            | None -> 
                                if List.isEmpty untried then None
                                else tryTile untried.Tail
                        tryTile l
                
            //else ()
            match m with
            | Some move -> 
                debugPrint (sprintf "Player %d -> Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.
                send cstream (SMPlay move)
            | None -> send cstream SMPass

            let msg = recv cstream
            match m with
            | Some move -> debugPrint (sprintf "Player %d <- Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.
            | None -> ()

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
        