let rec pli2 jeu1 jeu2 tas1 tas2 nb_plis =
  match (jeu1, jeu2) with
  | [], _ | _, [] -> nb_plis
  | c1 :: l1, c2 :: l2 -> (
      if c1 > c2 then
        pli2 (l1 @ (c1 :: c2 :: tas1) @ tas2) l2 [] [] (nb_plis + 1)
      else if c2 > c1 then
        pli2 l1 (l2 @ (c2 :: c1 :: tas2) @ tas1) [] [] (nb_plis + 1)
      else
        match (l1, l2) with
        | [], _ | _, [] -> nb_plis + 1
        | c11 :: l11, c22 :: l22 ->
            pli2 l11 l22 (tas1 @ [ c1; c11 ]) (tas2 @ [ c2; c22 ]) (nb_plis + 1)
      )

let rnd_jeu n = Array.init n (fun _ -> Random.int 55) |> Array.to_list

let pliq jeu1 jeu2 tas1 tas2 =
  let rec loop nb_plis =
    match (Queue.take_opt jeu1, Queue.take_opt jeu2) with
    | None, _ | _, None -> nb_plis
    | Some c1, Some c2 ->
        if c1 > c2 then (
          Queue.add c1 jeu1;
          Queue.add c2 jeu1;
          Queue.transfer tas1 jeu1;
          Queue.transfer tas2 jeu1)
        else if c1 < c2 then (
          Queue.add c2 jeu2;
          Queue.add c1 jeu2;
          Queue.transfer tas2 jeu2;
          Queue.transfer tas1 jeu2)
        else (
          Queue.add c1 tas1;
          Queue.add c2 tas2;
          Option.iter (fun c -> Queue.add c tas1) (Queue.take_opt jeu1);
          Option.iter (fun c -> Queue.add c tas2) (Queue.take_opt jeu2));
        loop (nb_plis + 1)
  in
  loop 0

let queue_of_list l =
  let q = Queue.create () in
  List.iter (fun c -> Queue.add c q) l;
  q

let dq_of_n lst =
  let open Bro_deque in
  let rec loop dq lst =
    match lst with
    | [] -> dq
    | x :: xs ->
        let dq = BroDeque.snoc x dq in
        loop dq xs
  in
  loop BroDeque.empty lst

let rec plib jeu1 jeu2 tas1 tas2 nb_plis =
  let open Bro_deque in
  match (BroDeque.take_front jeu1, BroDeque.take_front jeu2) with
  | None, _ | _, None -> nb_plis
  | Some (c1, l1), Some (c2, l2) -> (
      if c1 > c2 then
        let new_l1 = BroDeque.cons_many [| c1; c2 |] tas1 in
        let new_l1 = BroDeque.cons_deque new_l1 tas2 in
        let new_l1 = BroDeque.cons_deque l1 new_l1 in
        plib new_l1 l2 BroDeque.empty BroDeque.empty (nb_plis + 1)
      else if c2 > c1 then
        let new_l2 = BroDeque.cons_many [| c2; c1 |] tas2 in
        let new_l2 = BroDeque.cons_deque new_l2 tas1 in
        let new_l2 = BroDeque.cons_deque l2 new_l2 in
        plib l1 new_l2 BroDeque.empty BroDeque.empty (nb_plis + 1)
      else
        match (BroDeque.take_front l1, BroDeque.take_front l2) with
        | None, _ | _, None -> nb_plis + 1
        | Some (c11, l11), Some (c22, l22) ->
            let tas1 = BroDeque.snoc_many [| c1; c11 |] tas1 in
            let tas2 = BroDeque.snoc_many [| c2; c22 |] tas2 in
            plib l11 l22 tas1 tas2 (nb_plis + 1))

let time_it f =
  let t = Sys.time () in
  f ();
  print_endline (" Time = " ^ string_of_float (Sys.time () -. t))

let bench () =
  let n = 1000 in
  let jeu1 = rnd_jeu n in
  let jeu2 = rnd_jeu n in
  time_it (fun () -> pli2 jeu1 jeu2 [] [] 0 |> print_int);

  let jeu1_q = queue_of_list jeu1 in
  let jeu2_q = queue_of_list jeu2 in
  time_it (fun () ->
      pliq jeu1_q jeu2_q (Queue.create ()) (Queue.create ()) |> print_int);

  let open Bro_deque in
  let jeu1 = dq_of_n jeu1 in
  let jeu2 = dq_of_n jeu2 in
  time_it (fun () ->
      plib jeu1 jeu2 BroDeque.empty BroDeque.empty 0 |> print_int)
