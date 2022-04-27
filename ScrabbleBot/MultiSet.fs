// Insert your MultiSet.fs file here. All modules must be internal

module internal MultiSet
    type MultiSet<'a when 'a : comparison> = M of Map<'a,uint32>
    
    let empty = M Map.empty
    let isEmpty (M s) = s.IsEmpty
    let size (M s) = Map.fold (fun st k v -> st + v) 0u s
    let contains a (M s) = 
        match s.TryFind a with
        | Some x -> true
        | None -> false
    let numItems a (M s) = 
        match s.TryFind a with
        | Some x -> x
        | None -> 0u
    let add a n (M s) = 
        match s.TryFind a with
        | Some x -> M (s.Add (a,x+n))
        | None -> M (s.Add (a,n))
    let addSingle a m = add a 1u m
    let remove a n (M s) = 
        match s.TryFind a with
        | Some x when x>n -> M (s.Add (a,x-n))
        | _ -> M (s.Remove a)
    let removeSingle a m = remove a 1u m
    let fold f acc (M s) = Map.fold f acc s
    let foldBack f (M s) acc = Map.foldBack f s acc
    
    // Yellow
    
    let ofList lst = List.fold (fun m v -> addSingle v m) empty lst
    let rec toList m = 
        let rec tol l k n =
            match n with
            | n when n > 0u -> k::(tol l k (n-1u))
            | _ -> l
        foldBack (fun k v l -> tol l k v) m []
    let map f (M s) = Map.fold (fun m k v -> add (f k) v m) empty s
    let union (M s) (M p) = M (Map.fold (fun (m:Map<'a,uint32>) k v -> 
            match m.TryFind k with
            | Some x when x >= v -> m
            | _ -> m.Add (k,v) ) s p)
    let sum m1 m2 = fold (fun m k v -> add k v m) m1 m2
    let subtract m1 m2 = fold (fun m k v -> remove k v m) m1 m2
    let intersection (M s) (M p) = M (Map.fold (fun m k v ->
        match p.TryFind k with
        | Some x -> m.Add (k,(min v x))
        | None -> m ) Map.empty s)