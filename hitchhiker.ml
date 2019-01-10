module type OrderedType = sig
  type t

  val compare : t -> t -> int
end

module Make (Ord : OrderedType) = struct
  type key = Ord.t

  type 'a t =
    | Leaf of (key * 'a) list
    | Node of (key * 'a t) list * (key * 'a) list

  let max_children = 5
  let max_buffer = 5
  let () = assert (max_buffer <= max_children)

  let empty = Leaf []

  let is_empty t =
    match t with
    | Leaf [] -> true
    | _ -> false

  let halve l =
    let n = List.length l in
    let rec loop i buff l =
      match l with
      | [] -> [], []
      | h::t ->
          if i <= n/2 then
            loop (i+1) (h::buff) t
          else
            buff, l
    in
    let first_half, second_half = loop 0 [] l in
    fst (List.hd first_half), List.rev first_half, fst (List.hd (List.rev second_half)), second_half

  let rec split_buf lb k out1 out2 =
    match lb with
    | [] -> out1, out2
    | (k', v)::lb' ->
      if Ord.compare k' k <= 0 then
        split_buf lb' k ((k', v)::out1) out2
      else
        split_buf lb' k out1 ((k', v)::out2)

  let split t =
    match t with
    | Leaf l ->
      let k1, l1, k2, l2 = halve l in
      (k1, Leaf l1), (k2, Leaf l2)
    | Node (lt, lb) ->
      let k1, lt1, k2, lt2 = halve lt in
      let lb1, lb2 = split_buf lb k1 [] [] in
      (k1, Node (lt1, lb1)), (k2, Node (lt2, lb2))
  
  let merge t t' =
    match t, t' with
    | Leaf l, Leaf l' -> Leaf (List.append l l')
    | Node (lt, lb), Node (lt', lb') -> Node (List.append lt lt', List.append lb lb')
    | _ -> assert false
  
  let rec merge_l lt =
    match lt with
    | [] -> []
    | [(k', t')] -> lt
    | (k', t')::(((k'', t'')::lt'') as lt') ->
      let get_size t = match t with | Leaf l -> List.length l | Node (lt, _) -> List.length lt in
      if (get_size t') + (get_size t'') <= max_children then
        (k'', merge t' t'')::lt''
      else
        (k', t')::(merge_l lt')

  let needs_split t =
    match t with
    | Leaf l -> List.length l > max_children
    | Node (lt, _) -> List.length lt > max_children
  
  let needs_flush lb = List.length lb > max_buffer
  
  let rec add_nonfull ldata t =
    match t with
    | Leaf l ->
      let rec loop ldata l =
        match l with
        | [] -> ldata
        | h::t -> begin
          match ldata with
          | [] -> l
          | (k, data)::ldata' ->
            let c = Ord.compare k (fst h) in
            if c < 0 then
              (k, data)::(loop ldata' l)
            else if c = 0 then
              (k, data)::(loop ldata' t)
            else
              h::(loop ldata t)
        end
      in
      Leaf (loop ldata l)
    | Node (lt, lb) ->
      let lb = List.sort (fun (k, _) (k', _) -> Ord.compare k k') (List.rev_append ldata lb) in
      if needs_flush lb then
        Node (flush lb lt, [])
      else
        Node (lt, lb)
  and flush lb lt =
    match lb with
    | [] -> lt
    | _ -> begin
      match lt with
      | [] -> assert false
      | (k, t)::lt' ->
        let lflush, lb' = List.partition (fun (kb, _) -> Ord.compare kb k < 0 || lt' = []) lb in
        let newk =
          List.fold_left
            (fun out (k, _) -> if Ord.compare out k < 0 then k else out)
            k lflush
        in
        let t' = add_nonfull lflush t in
        if needs_split t' then
          let n1, n2 = split t' in
          n1::n2::(flush lb' lt')
        else
          (newk, t')::(flush lb' lt')
    end

  let add k data t =
    let nonfull =
      if needs_split t then
        let n1, n2 = split t in
        Node ([n1; n2], [])
      else t
    in
    add_nonfull [k, data] nonfull

  let rec remove_l k lt =
    match lt with
    | [] -> []
    | (k', t')::lt' ->
      if Ord.compare k k' < 0 then
        (k', remove k t')::lt'
      else
        (k', t')::(remove_l k lt')
  and remove k t =
    match t with
    | Leaf l -> Leaf (List.remove_assoc k l)
    | Node (lt, lb) ->
      if List.mem_assoc k lb then
        Node (lt, List.remove_assoc k lb)
      else
        Node (merge_l (remove_l k lt), lb)
      
  let rec find_opt k t =
    match t with
    | Leaf l -> List.assoc_opt k l
    | Node (lt, lb) -> begin
      try
        Some (List.assoc k lb)
      with Not_found ->
        let rec loop lt =
          match lt with
          | [] -> None
          | (k', _)::lt' when Ord.compare k k' > 0 -> loop lt'
          | (_, t') :: _ -> find_opt k t'
        in loop lt
    end

  let find x t =
    match find_opt x t with
    | Some data -> data
    | None -> raise Not_found

  let bindings t =
    let rec loop t =
      match t with
      | Leaf l -> l
      | Node (lt, lb) -> List.rev_append lb (List.flatten (List.map (fun (_, t) -> loop t) lt))
    in List.sort (fun (k, _) (k', _) -> Ord.compare k k') (loop t)
  
  let to_string t fk fv =
    let unit_tab = "  " in
    let buff = Buffer.create 10 in
    let rec loop t tab =
      match t with
      | Leaf l  ->
        Buffer.add_string buff (tab ^ "[");
        List.iter
          (fun (k, v) ->
            Buffer.add_string buff ((fk k) ^ " : " ^ (fv v) ^ " ; "))
          l;
          Buffer.add_string buff "]"
      | Node (lt, lb) ->
        List.iter
          (fun (k, t') ->
            Buffer.add_string buff (tab ^ (fk k) ^ " : \n");
            loop t' (tab ^ unit_tab);
            Buffer.add_string buff "\n")
          lt;
        Buffer.add_string buff (tab ^ "[");
        List.iter
          (fun (k, v) ->
            Buffer.add_string buff ((fk k) ^ " : " ^ (fv v) ^ " ; "))
          lb;
        Buffer.add_string buff "]\n"
    in
    loop t "";
    Buffer.contents buff
end

module T = Make(struct type t = int let compare = compare end)


let n = 6

let t1 = ref T.empty
let () = for k = 0 to n do
  t1 := T.add k (string_of_int k) !t1
done

let t2 = ref T.empty
let () = for k = n downto 0 do
  t2 := T.add k (string_of_int k) !t2
done

let () =
  print_endline "t1:";
  print_endline (T.to_string !t1 string_of_int (fun s -> s));
  print_endline "t2:";
  print_endline (T.to_string !t2 string_of_int (fun s -> s));
  print_endline (string_of_bool (!t1 = !t2));
  print_endline (string_of_bool (T.bindings !t1 = T.bindings !t2))

let t = ref T.empty
let () = for k = 0 to 20 do
  t := T.add k k !t
done

let () =
  print_endline "t:";
  print_endline (T.to_string !t string_of_int (fun _ -> ""))

let () = t := T.remove 6 (T.remove 5 (T.remove 10 !t))

let () =
  print_endline "t:";
  print_endline (T.to_string !t string_of_int (fun _ -> ""))