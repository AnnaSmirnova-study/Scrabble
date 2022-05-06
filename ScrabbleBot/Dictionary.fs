module Dictionary
    type Dict = D of Map<char,bool * Dict>

    let empty (a:unit) = D Map.empty
    let step c (D d) = Map.tryFind c d
    let update k v (D d) = D (Map.add k v d)

    let insert (s: string) d = 
        let rec aux (s:char list) d = 
            match step s.Head d with
            | Some (b,node) -> 
                match s.Tail with
                | [] -> update s.Head (true, node) d
                | tail -> update s.Head (b, aux tail node) d
            | None -> 
                match s.Tail with
                | [] -> update s.Head (true, empty ()) d
                | tail -> update s.Head (false, aux tail (empty ())) d
        aux (List.ofSeq s) d

    let lookup (s: string) d = 
        let rec aux (s:char list) d =
            match step s.Head d with
            | Some (b, node) -> 
                match s.Tail with
                | [] -> b
                | tail -> aux tail node
            | None -> false
        aux (List.ofSeq s) d
