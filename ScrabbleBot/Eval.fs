// Insert your updated Eval.fs file here from Assignment 7. All modules must be internal.

module internal Eval

    open StateMonad
    
    (* Code for testing *)
    
    let hello = [('H',4); ('E',1); ('L',1); ('L',1); ('O',1)] 
    let state = mkState [("x", 5); ("y", 42)] hello ["_pos_"; "_result_"]
    let emptyState = mkState [] [] []
        
    let add a b = a >>= (fun av -> b >>= (fun bv -> ret (av+bv)))
    let sub a b = a >>= (fun av -> b >>= (fun bv -> ret (av-bv)))
    let mul a b = a >>= (fun av -> b >>= (fun bv -> ret (av*bv)))
    let div a b = a >>= (fun av -> b >>= (fun bv -> if bv > 0 then ret (av/bv) else fail DivisionByZero))   
    let modd a b = a >>= (fun av -> b >>= (fun bv -> if bv > 0 then ret (av%bv) else fail DivisionByZero))  
    
    type aExp =
        | N of int
        | V of string
        | WL
        | PV of aExp
        | Add of aExp * aExp
        | Sub of aExp * aExp
        | Mul of aExp * aExp
        | Div of aExp * aExp
        | Mod of aExp * aExp
        | CharToInt of cExp
    
    and cExp =
        | C  of char  (* Character value *)
        | CV of aExp  (* Character lookup at word index *)
        | ToUpper of cExp
        | ToLower of cExp
        | IntToChar of aExp
    
    type bExp =             
        | TT                   (* true *)
        | FF                   (* false *)
    
        | AEq of aExp * aExp   (* numeric equality *)
        | ALt of aExp * aExp   (* numeric less than *)
    
        | Not of bExp          (* boolean not *)
        | Conj of bExp * bExp  (* boolean conjunction *)
    
        | IsVowel of cExp      (* check for vowel *)
        | IsLetter of cExp     (* check for letter *)
        | IsDigit of cExp      (* check for digit *)
    
    let (.+.) a b = Add (a, b)
    let (.-.) a b = Sub (a, b)
    let (.*.) a b = Mul (a, b)
    let (./.) a b = Div (a, b)
    let (.%.) a b = Mod (a, b)
    
    let (~~) b = Not b
    let (.&&.) b1 b2 = Conj (b1, b2)
    let (.||.) b1 b2 = ~~(~~b1 .&&. ~~b2)       (* boolean disjunction *)
    let (.->.) b1 b2 = (~~b1) .||. b2           (* boolean implication *) 
           
    let (.=.) a b = AEq (a, b)   
    let (.<.) a b = ALt (a, b)   
    let (.<>.) a b = ~~(a .=. b)
    let (.<=.) a b = a .<. b .||. ~~(a .<>. b)
    let (.>=.) a b = ~~(a .<. b)                (* numeric greater than or equal to *)
    let (.>.) a b = ~~(a .=. b) .&&. (a .>=. b) (* numeric greater than *)    
    
    let isVowel (c: char) = "aeiouAEIOU".Contains(c)
    
    let rec evalA b = 
        match b with
        | N i -> ret i
        | V k -> lookup k
        | WL -> wordLength
        | PV pos -> evalA pos >>= pointValue
        | Add (n,m) -> add (evalA n) (evalA m)
        | Sub (n,m) -> sub (evalA n) (evalA m)
        | Mul (n,m) -> mul (evalA n) (evalA m)
        | Div (n,m) -> div (evalA n) (evalA m)
        | Mod (n,m) -> modd (evalA n) (evalA m)
        | CharToInt c -> evalC c >>= (fun c -> ret (int c))
    and evalC c =
        match c with 
        | C c -> ret c
        | CV a -> evalA a >>= characterValue
        | ToUpper c -> evalC c >>= (fun c -> ret (System.Char.ToUpper c))
        | ToLower c -> evalC c >>= (fun c -> ret (System.Char.ToLower c))
        | IntToChar a -> evalA a >>= (fun a -> ret (char a))
    
    let arithEval a : SM<int> = evalA a
    
    let charEval c : SM<char> = evalC c    
    
    let boolEval b : SM<bool> = 
        let rec aux b =
            match b with
            | TT -> ret true
            | FF -> ret false
    
            | AEq (n,m) -> evalA n >>= (fun nv -> evalA m >>= (fun mv -> ret (nv = mv)))  (* numeric equality *)
            | ALt (n,m) -> evalA n >>= (fun nv -> evalA m >>= (fun mv -> ret (nv < mv)))   (* numeric less than *)
    
            | Not b -> aux b >>= (fun bv -> ret (not bv))          (* boolean not *)
            | Conj (n,m) -> aux n >>= (fun nv -> aux m >>= (fun mv -> ret (nv && mv)))  (* boolean conjunction *)
    
            | IsVowel c -> evalC c >>= (fun cv -> ret (isVowel cv))      (* check for vowel *)
            | IsLetter c -> evalC c >>= (fun cv -> ret (System.Char.IsLetter cv))     (* check for letter *)
            | IsDigit c -> evalC c >>= (fun cv -> ret (System.Char.IsDigit cv))
        aux b
    
    type stm =                (* statements *)
    | Declare of string       (* variable declaration *)
    | Ass of string * aExp    (* variable assignment *)
    | Skip                    (* nop *)
    | Seq of stm * stm        (* sequential composition *)
    | ITE of bExp * stm * stm (* if-then-else statement *)
    | While of bExp * stm     (* while statement *)
    
    let rec stmntEval stmnt : SM<unit> = 
        match stmnt with
        | Declare s -> declare s
        | Skip -> ret ()
        | Ass (s,a) -> arithEval a >>= update s
        | Seq (stm1,stm2) -> stmntEval stm1 >>>= stmntEval stm2
        | ITE (b,stm1,stm2) -> push >>>= boolEval b >>= (fun bv -> if bv then stmntEval stm1 else stmntEval stm2) >>>= pop
        | While (b,stm) -> push >>>= boolEval b >>= (fun bv -> if bv 
                                                                then stmntEval stm >>>= stmntEval (While (b,stm))
                                                                else stmntEval Skip) >>>= pop
    
(* Part 3 (Optional) *)
    
    type StateBuilder() =
    
        member this.Bind(f, x)    = f >>= x
        member this.Return(x)     = ret x
        member this.ReturnFrom(x) = x
        member this.Delay(f)      = f ()
        member this.Combine(a, b) = a >>= (fun _ -> b)
            
    let prog = new StateBuilder()
    
    let arithEval2 a = failwith "Not implemented"
    let charEval2 c = failwith "Not implemented"
    let rec boolEval2 b = failwith "Not implemented"
    
    let stmntEval2 stm = failwith "Not implemented"
    
(* Part 4 (Optional) *) 
    
    type word = (char * int) list
    type squareFun = word -> int -> int -> Result<int, Error>
    
    let stmntToSquareFun stm : squareFun = fun word pos acc -> 
           let st = mkState [("_pos_", pos); ("_acc_", acc); ("_result_", 0)] word ["_pos_"; "_acc_"; "_result_"] 
           let sm = stmntEval stm >>>= arithEval (V "_result_")
           evalSM st sm
    
    
    type coord = int * int
    
    type boardFun = coord -> Result<squareFun option, Error> 
    
    let stmntToBoardFun stm m = fun ((x,y):coord) ->
        let st = mkState [("_x_", x); ("_y_", y); ("_result_", 0)] [] ["_x_"; "_y_"; "_result_"] 
        let sm = stmntEval stm >>>= arithEval (V "_result_") >>= fun id -> ret (Map.tryFind id m)
        evalSM st sm
    
    type board = {
        center        : coord
        defaultSquare : squareFun
        squares       : boardFun
    }
    
    let mkBoard c defaultSq boardStmnt ids = failwith "Not implemented"

