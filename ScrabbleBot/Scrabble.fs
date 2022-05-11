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
    type tile = (uint32 * (char * int))

    let tileVal ((_,(_,v)):tile) = v
    let tileId ((id,_):tile) = id
    

    type state = {
        board         : Parser.board
        dict          : ScrabbleUtil.Dictionary.Dict
        playerNumber  : uint32
        numPlayers    : uint32
        hand          : MultiSet.MultiSet<uint32>
        tiles         : Map<coord,tile>
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

    // If square is free returns None, if taken returns Some (square, tile)
    let checkSquareFree coords st = st.board.squares coords |> fun (StateMonad.Success sqr) -> sqr |>
        function
        | Some sqr -> Map.tryFind coords st.tiles |> Option.map (fun tile -> (sqr,tile))
        | None -> None
        
    // let checkDirection <- maybe we can try make a word and then check is it possible to put it?
    // or maybe it's easier to just check everytime we want put more letters 
    
    // just check is this word exist or not
    let checkWord word = Dictionary.lookup word
    

module internal algorithm =
    let findMove (st: State.state) =
        st.board.squares
        
        // I WILL EXPLAIN IT TOMORROW
        
        // good question: how we find first square to start building a word?))
        // maybe we can start from random from last move / (0, 0)
        
        //let tiles = List.fold (fun acc (coords,tile) -> Map.add coords tile acc) st.tiles ms
        
//        for _ in st.hand do
//            let answer = "" // acc for word
//            
//            // Option.count return zero if the option is None -> square is free 
//            if Option.count (State.checkSquareFree (0, 0) st) = 0
//                // first time we always go down, maybe we can make "flag" and change it every move? 0 - go down, 1 - go up
//                then None
//            else None

    type Direction =
        | Right = 0
        | Down = 1

    let checkSquaresSideBefore (x,y) dir st =
        match dir with
        | Direction.Right -> State.checkSquareFree (x,y-1) st
        | Direction.Down -> State.checkSquareFree (x-1,y) st

    let checkSquaresSideAfter (x,y) dir st =
        match dir with
        | Direction.Right -> State.checkSquareFree (x,y+1) st
        | Direction.Down -> State.checkSquareFree (x+1,y) st

    let shouldUseSquare coords dir st =
        match checkSquaresSideBefore coords dir st with
        | Some _ -> false
        | None -> 
            match checkSquaresSideAfter coords dir st with
            | Some _ -> false
            | None -> true
            


    
    (*
    Mutually recursive function.
    "find" checks if the given letter exists in the current branch of the trie.
    If it is the end of the word, the accumulator is returned.
    If it does not exist, None is returned.
    If it exists but is not the end of a word, checkEach is called on the rest of the hand.

    "checkEach" calls "find" on each letter in the hand, until a complete word is returned or there are no more letters.
    *)

    let rec find (c: uint32) dict (hand: uint32 list) acc = 
        match Dictionary.step (char c) dict with
        | Some (b, dict') -> 
            if b then Some (MultiSet.addSingle c acc)
            else 
                let acc' = MultiSet.addSingle c acc
                checkEach dict' hand acc'
        | None -> None

    and checkEach dict hand acc = 
        match find hand.Head dict hand.Tail acc with
        | Some acc' -> Some acc'
        | None -> 
            if hand.Tail.IsEmpty 
            then None 
            else checkEach dict hand.Tail acc



module Scrabble =
    open System.Threading

    let playGame cstream pieces (st : State.state) =

        let rec aux (st : State.state) =
            Print.printHand pieces (State.hand st)

            // remove the force print when you move on from manual input (or when you have learnt the format)
            if st.playerTurn = st.playerNumber then
                // forcePrint "Input move (format '(<x-coordinate> <y-coordinate>
                // <piece id><character><point-value> )*', note the absence of space between the last inputs)\n\n"
                
                let input =  System.Console.ReadLine()
                let move = RegEx.parseMove input

                debugPrint (sprintf "Player %d -> Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.
                send cstream (SMPlay move)
                
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
                let st' = State.mkState st.board st.dict st.playerNumber st.numPlayers hand tiles (State.updPlayerTurn st)
                aux st'

            | RCM (CMPlayed (pid, ms, points)) ->
                (* Successful play by other player. Update your state *)

                (* New state *)
                let st' = State.mkState st.board st.dict st.playerNumber st.numPlayers st.hand st.tiles (State.updPlayerTurn st)
                aux st'

            | RCM (CMPlayFailed (pid, ms)) ->
                (* Failed play. Update your state *)
                let st' = State.mkState st.board st.dict st.playerNumber st.numPlayers st.hand st.tiles (State.updPlayerTurn st)
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

        fun () -> playGame cstream tiles (State.mkState board dict playerNumber numPlayers handSet Map.empty playerTurn)
        