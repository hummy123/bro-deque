module type BRO_DEQUE = sig
  type 'a t

  val empty : 'a t
  val singleton : 'a -> 'a t
  val is_empty : 'a t -> bool
  val size : 'a t -> int
  val cons : 'a -> 'a t -> 'a t
  val cons_many : 'a array -> 'a t -> 'a t
  val snoc : 'a -> 'a t -> 'a t
  val snoc_many : 'a array -> 'a t -> 'a t
  val front : 'a t -> 'a option
  val back : 'a t -> 'a option
  val remove_front : 'a t -> 'a t
  val remove_back : 'a t -> 'a t
  val get_at : int -> 'a t -> 'a option
  val insert_at : int -> 'a -> 'a t -> 'a t
  val remove_at : int -> 'a t -> 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc
  val fold_right : ('a -> 'acc -> 'acc) -> 'acc -> 'a t -> 'acc
end

module BroDeque : BRO_DEQUE = struct
  (* There are two parts to the data structure in this module: 
   * a balanced tree called a body containing elements between the front and back,
   * and a wrapper around the body with head and tail fields which each contain an array.

   * Below is the type of the body in the deque.

   * It uses a kind of self-balancing binary trees 
   * which Ralf Hinze wrote about at the following link: 
   * https://www.cs.ox.ac.uk/ralf.hinze/publications/Brother12.pdf .

   * There are a few modifications to the datatype to make it rope-like 
   * and more suitable for contiguous elements:
   * 1. Instead of internal nodes (which point to other nodes) holding data 
        like in a normal binary tree, the internal nodes hold size metadata, 
        with two integers indicating the number of elements on the left and right subtree
        respectively. This is represented by the N2 case. 
   * 2. With only metadata left at the internal nodes, the leaves hold arrays of contiguous data.

   * These two changes make the data structure similar to a rope, 
   * which is a kind of binary tree for representing large strings. *)
  type 'a body =
    | N0 of 'a array
    | N1 of 'a body
    | N2 of 'a body * int * int * 'a body
    | L2 of 'a array * 'a array
    | N3 of 'a body * 'a body * 'a body

  (* The target_length specifies the maximum number of items allowed in an array,
     and 32 seems like a good choice as this is also the number used in both
     Clojure's persistent vector and in Relaxed Radix Balanced Trees. *)
  let target_length = 32

  let rec fold_left_body f acc = function
    | N2 (l, _, _, r) ->
        let acc = fold_left_body f acc l in
        fold_left_body f acc r
    | N1 t -> fold_left_body f acc t
    | N0 arr -> Array.fold_left f acc arr
    | _ -> failwith "bro_deque fold_left: aux constructor"

  let rec fold_right_body f acc = function
    | N2 (l, _, _, r) ->
        let acc = fold_right_body f acc r in
        fold_right_body f acc l
    | N1 t -> fold_right_body f acc t
    | N0 arr -> Array.fold_right f arr acc
    | _ -> failwith "bro_deque fold_right: aux constructor"

  let rec map_body f = function
    | N0 arr ->
        let arr = Array.map f arr in
        N0 arr
    | N1 t ->
        let t = map_body f t in
        N1 t
    | N2 (l, lm, rm, r) ->
        let l = map_body f l in
        let r = map_body f r in
        N2 (l, lm, rm, r)
    | _ -> failwith "bro_deque map: aux constructor"

  let is_body_empty = function N0 arr -> Array.length arr = 0 | _ -> false

  (* Returns the number of elements in the given tree/subtree. *)
  let rec size_body = function
    | N0 arr -> Array.length arr
    | N1 t -> size_body t
    | N2 (_, lm, rm, _) -> lm + rm
    (* I believe the size function is never called on the aux constructures. *)
    | N3 (t1, t2, t3) -> size_body t1 + size_body t2 + size_body t3
    | L2 (a1, a2) -> Array.length a1 + Array.length a2

  (* Standard balancing function when inserting into the left on a 1-2 Brother Tree. 
   * The only difference is that the size_body function is used to maintain internal node metadata. *)
  let ins_n2_left l r =
    match (l, r) with
    | L2 (a1, a2), t3 -> N3 (N0 a1, N0 a2, t3)
    | N3 (t1, t2, t3), N1 t4 ->
        let left = N2 (t1, size_body t1, size_body t2, t2) in
        let right = N2 (t3, size_body t3, size_body t4, t4) in
        N2 (left, size_body left, size_body right, right)
    | N3 (t1, t2, t3), t4 ->
        let left = N2 (t1, size_body t1, size_body t2, t2) in
        N3 (left, N1 t3, t4)
    | l, r -> N2 (l, size_body l, size_body r, r)

  (* Standard balancing function when deleting from the left on a 1-2 Brother Tree.
   * The only difference is that the size_body is used to maintain internal node metadata. *)
  let del_n2_left l r =
    match (l, r) with
    | N1 t1, N1 t2 -> N1 (N2 (t1, size_body t1, size_body t2, t2))
    | N1 (N1 t1), N2 (N1 t2, _, _, (N2 _ as t3)) ->
        let left = N2 (t1, size_body t1, size_body t2, t2) in
        let inner = N2 (left, size_body left, size_body t3, t3) in
        N1 inner
    | N1 (N1 t1), N2 (N2 (t2, _, _, t3), _, _, N1 t4) ->
        let left = N2 (t1, size_body t1, size_body t2, t2) in
        let right = N2 (t3, size_body t3, size_body t4, t4) in
        let inner = N2 (left, size_body left, size_body right, right) in
        N1 inner
    | N1 (N1 _ as t1), N2 ((N2 _ as t2), _, _, (N2 _ as t3)) ->
        let left = N2 (t1, size_body t1, size_body t2, t2) in
        let right = N1 t3 in
        N2 (left, size_body left, size_body t3, right)
    | l, r -> N2 (l, size_body l, size_body r, r)

  (* Standard balancing function when inserting into the right on a 1-2 Brother Tree. *)
  let ins_n2_right l r =
    match (l, r) with
    | t1, L2 (a1, a2) -> N3 (t1, N0 a1, N0 a2)
    | N1 t1, N3 (t2, t3, t4) ->
        let left = N2 (t1, size_body t1, size_body t2, t2) in
        let right = N2 (t3, size_body t3, size_body t4, t4) in
        N2 (left, size_body left, size_body right, right)
    | t1, N3 (t2, t3, t4) ->
        let right = N2 (t3, size_body t3, size_body t4, t4) in
        N3 (t1, N1 t2, right)
    | l, r -> N2 (l, size_body l, size_body r, r)

  (* Standard balancing function when deleting from the right on a 1-2 Brother Tree. *)
  let del_n2_right l r =
    match (l, r) with
    | N2 (N1 t1, _, _, N2 (t2, _, _, t3)), N1 (N1 t4) ->
        let left = N2 (t1, size_body t1, size_body t2, t2) in
        let right = N2 (t3, size_body t3, size_body t4, t4) in
        let inner = N2 (left, size_body left, size_body right, right) in
        N1 inner
    | N2 ((N2 _ as t1), _, _, N1 t2), N1 (N1 t3) ->
        let right = N2 (t2, size_body t2, size_body t3, t3) in
        let inner = N2 (t1, size_body t1, size_body right, right) in
        N1 inner
    | N2 ((N2 _ as t1), _, _, (N2 _ as t2)), N1 (N1 _ as t3) ->
        let left = N1 t1 in
        let right = N2 (t2, size_body t2, size_body t3, t3) in
        N2 (left, size_body left, size_body right, right)
    | l, r -> N2 (l, size_body l, size_body r, r)

  (* Balancing function called when deleting a node. *)
  let del_root = function N1 t -> t | t -> t

  (* Balancing function called when inserting a node. *)
  let ins_root = function
    | L2 (a1, a2) -> N2 (N0 a1, Array.length a1, Array.length a2, N0 a2)
    | N3 (t1, t2, t3) ->
        let left = N2 (t1, size_body t1, size_body t2, t2) in
        N2 (left, size_body left, size_body t3, t3)
    | t -> t

  (* Smart constructor for 1-2 Brother trees when inserting in the N1 case. *)
  let ins_n1 = function
    | L2 (a1, a2) -> N2 (N0 a1, Array.length a1, Array.length a2, N0 a2)
    | N3 (t1, t2, t3) ->
        let left = N2 (t1, size_body t1, size_body t2, t2) in
        N2 (left, size_body left, size_body t3, t3)
    | t -> N1 t

  (* Prepends an array to the body, calling relevant balancing functions if needed. *)
  let rec cons_body_internal new_arr = function
    | N0 arr ->
        if Array.length new_arr + Array.length arr < target_length then
          N0 (Array.append new_arr arr)
        else L2 (new_arr, arr)
    | N1 t ->
        let t = cons_body_internal new_arr t in
        ins_n1 t
    | N2 (l, _, _, r) ->
        let l = cons_body_internal new_arr l in
        ins_n2_left l r
    | _ -> failwith "bro_deque cons_body_internal: aux constructor"

  (* Prepends an array to the body and calls the relevant root-balancing function. *)
  let cons_body arr body = cons_body_internal arr body |> ins_root

  (* Appends an array to the body, calling relevant balancing functions if needed. *)
  let rec snoc_body_internal new_arr = function
    | N0 arr ->
        if Array.length new_arr + Array.length arr < target_length then
          N0 (Array.append arr new_arr)
        else L2 (arr, new_arr)
    | N1 t ->
        let t = snoc_body_internal new_arr t in
        ins_n1 t
    | N2 (l, _, _, r) ->
        let r = snoc_body_internal new_arr r in
        ins_n2_right l r
    | _ -> failwith "bro_deque snoc_body_internal: aux constructor"

  (* Appends an array to the body and calls the relevant root-balancing function. *)
  let snoc_body arr body = snoc_body_internal arr body |> ins_root

  (* Removes the front element from the body, or does nothing if the body is empty. *)
  let rec remove_front_body_internal = function
    | N0 arr as node ->
        if Array.length arr > 0 then N0 (Array.sub arr 1 (Array.length arr - 1))
        else
          (* If there is nothing to remove, then simply don't remove anything. *)
          node
    | N1 t ->
        let t = remove_front_body_internal t in
        N1 t
    | N2 (l, _, _, r) ->
        let l = remove_front_body_internal l in
        del_n2_left l r
    | _ -> failwith "bro_deque remove_front_body_internal aux constructor"

  (* Removes the front element from the body if body is not empty,
     calling the relevant root-balancing function. *)
  let remove_front_body body = remove_front_body_internal body |> del_root

  (* Removes the front element from the body, or does nothing if the body is empty. *)
  let rec remove_back_body_internal = function
    | N0 arr as node ->
        if Array.length arr > 0 then N0 (Array.sub arr 0 (Array.length arr - 1))
        else (* Do nothing if there are no elements to remove. *)
          node
    | N1 t ->
        let t = remove_back_body_internal t in
        N1 t
    | N2 (l, _, _, r) ->
        let r = remove_back_body_internal r in
        del_n2_right l r
    | _ -> failwith "bro_deque remove_back_body_internal aux constructor"

  (* Removes the front element from the body if body is not empty,
     calling the relevant root-balancing function. *)
  let remove_back_body body = remove_back_body_internal body |> del_root

  let rec front_body = function
    | N0 arr ->
        if Array.length arr > 0 then Some (Array.unsafe_get arr 0) else None
    | N1 t -> front_body t
    | N2 (l, _, _, _) -> front_body l
    | _ -> failwith "bro_deque front_body aux constructor"

  let rec back_body = function
    | N0 arr ->
        if Array.length arr > 0 then
          Some (Array.unsafe_get arr (Array.length arr - 1))
        else None
    | N1 t -> back_body t
    | N2 (_, _, _, r) -> back_body r
    | _ -> failwith "bro_deque back_body aux constructor"

  let rec get_at_body idx = function
    | N0 arr ->
        if idx >= 0 && idx < Array.length arr then
          Some (Array.unsafe_get arr idx)
        else None
    | N1 t -> get_at_body idx t
    | N2 (l, lm, _, r) ->
        (* This case uses the standard rope algorithm for searching:
           If the left weight/metadata is greater than the current position,
           then recurse to the left subtree.
           Else, subtract the left weight from the current position and then
           recurse to the right subtree. *)
        if lm > idx then get_at_body idx l else get_at_body (idx - lm) r
    | _ -> failwith "bro_deque get_at_body aux constructor"

  let is_less_than_target arr1 arr2 =
    Array.length arr1 + Array.length arr2 < target_length

  let rec insert_at_body_internal idx new_arr = function
    | N0 old_arr ->
        if idx <= 0 then
          if is_less_than_target old_arr new_arr then
            N0 (Array.append new_arr old_arr)
          else L2 (new_arr, old_arr)
        else if idx >= Array.length old_arr then
          if is_less_than_target old_arr new_arr then
            N0 (Array.append old_arr new_arr)
          else L2 (old_arr, new_arr)
        else
          let sub1 = Array.sub old_arr 0 idx in
          let sub2_len = Array.length old_arr - idx in
          let sub2 = Array.sub old_arr idx sub2_len in
          if is_less_than_target new_arr old_arr then
            N0 (Array.concat [ sub1; new_arr; sub2 ])
          else if idx + Array.length new_arr < target_length then
            L2 (Array.append sub1 new_arr, sub2)
          else if sub2_len + Array.length new_arr < target_length then
            L2 (sub1, Array.append new_arr sub2)
          else N3 (N0 sub1, N0 new_arr, N0 sub2)
    | N1 t -> insert_at_body_internal idx new_arr t |> ins_n1
    | N2 (l, lm, _, r) ->
        if idx < lm then
          let l = insert_at_body_internal idx new_arr l in
          ins_n2_left l r
        else
          let r = insert_at_body_internal (idx - lm) new_arr r in
          ins_n2_right l r
    | _ -> failwith "bro_deque insert_at_body_internal aux constructor"

  let insert_at_body idx new_arr body =
    insert_at_body_internal idx new_arr body |> ins_root

  (* The type del_action helps with figuring out how to balance after deleting from the body
   * at an arbitrary index.

   * Roughly, the problem is this: an array that is too large will be costly to modify.
   * So, if we are deleting from an especially large array, it would be helpful performance-wise
   * to split it into smaller arrays using the L2 constructor for adding nodes.
   * Unintuitively, an *element* deletion could therefore cause 
   * the *node* insertion balancing algorithm to occur. *)
  type del_action = Added | Deleted

  let rec del_at_body_internal idx = function
    | N0 arr ->
        if Array.length arr <= 1 then (N0 [||], Deleted)
        else if idx = 0 then
          (N0 (Array.sub arr 1 (Array.length arr - 1)), Deleted)
        else if idx = Array.length arr - 1 then
          (N0 (Array.sub arr 0 (Array.length arr - 1)), Deleted)
        else
          let sub1 = Array.sub arr 0 idx in
          let sub2_len = Array.length arr - idx in
          let sub2 = Array.sub arr idx sub2_len in
          if is_less_than_target sub1 sub2 then
            (N0 (Array.append sub1 sub2), Deleted)
          else (L2 (sub1, sub2), Added)
    | N1 t ->
        let t, action = del_at_body_internal idx t in
        let t = match action with Added -> ins_n1 t | _ -> N1 t in
        (t, action)
    | N2 (l, lm, _, r) -> (
        if idx < lm then
          let l, action = del_at_body_internal idx l in
          match action with
          | Added -> (ins_n2_left l r, action)
          | Deleted -> (del_n2_left l r, action)
        else
          let r, action = del_at_body_internal (idx - lm) r in
          match action with
          | Added -> (ins_n2_right l r, action)
          | Deleted -> (del_n2_right l r, action))
    | _ -> failwith "bro_deque del_at_body_internal aux constructor"

  let del_at_body idx body =
    let t, action = del_at_body_internal idx body in
    match action with Added -> ins_root t | Deleted -> del_root t

  (* Removes the start node in the body if any and returns its array to the caller,
     rebalancing as needed. *)
  let rec pop_body_start_internal = function
    | N0 arr -> (N0 [||], arr)
    | N1 t ->
        let t, arr = pop_body_start_internal t in
        (N1 t, arr)
    | N2 (l, _, _, r) ->
        let l, arr = pop_body_start_internal l in
        (del_n2_left l r, arr)
    | _ -> failwith "bro_deque pop_body_start_internal aux constructor"

  let pop_body_start body =
    let body, arr = pop_body_start_internal body in
    let body = del_root body in
    (body, arr)

  let rec pop_body_end_internal = function
    | N0 arr -> (N0 [||], arr)
    | N1 t ->
        let t, arr = pop_body_end_internal t in
        (N1 t, arr)
    | N2 (l, _, _, r) ->
        let r, arr = pop_body_end_internal r in
        (del_n2_right l r, arr)
    | _ -> failwith "bro_deque pop_body_end_internal aux constructor"

  let pop_body_end body =
    let body, arr = pop_body_end_internal body in
    let body = del_root body in
    (body, arr)

  (* This is the type of the deque. 
   * The goal of this implementation is O(1) access to the front and back,
   * and the data structure behind Clojure vectors gives a clue on how to do this. 

   * Clojure's persistent vector is an append-only data structure with a temporary "tail" array 
   * which is separete from the tree structure. When the tail is full (has 32 elements), 
   * it is appended to the tree and an empty array becomes the new tail. 

   * This deque works exactly the same way, except thaat it has a head array too
   * and uses a different tree data structure which supports insertion at any arbitrary location. *)
  type 'a t = {
    (* head means array preceding body *)
    head : 'a array;
    (* body means *)
    body : 'a body;
    (* tail means array following body *)
    tail : 'a array;
  }

  let empty = { head = [||]; tail = [||]; body = N0 [||] }
  let singleton x = { head = [| x |]; tail = [||]; body = N0 [||] }
  let is_empty dq = Array.length dq.head = 0 && Array.length dq.tail = 0
  let size dq = size_body dq.body + Array.length dq.head + Array.length dq.tail

  (*
      The logic for cons is:

      If we can fit this element into the head while staying under the target length,
      then add this element to the start of the head.

      Else, if the body is empty and the tail is also empty,
      then set the old head as the new tail and set the new element as the head.
      This second case ensures the head and tail are always full before we insert into the body,
      guaranteeing O(1) access to the front or back of the deque

      Else, cons the old head to the body and set the new element as the head.
  *)
  let cons el dq =
    if Array.length dq.head < target_length then
      let head = Array.append [| el |] dq.head in
      { dq with head }
    else if is_body_empty dq.body && Array.length dq.tail = 0 then
      let tail = dq.head in
      { dq with head = [| el |]; tail }
    else
      let body = cons_body dq.head dq.body in
      let head = [| el |] in
      { dq with head; body }

  let cons_many arr dq =
    if is_less_than_target dq.head arr then
      let head = Array.append arr dq.head in
      { dq with head }
    else if is_body_empty dq.body && Array.length dq.tail = 0 then
      let tail = dq.head in
      { dq with head = arr; tail }
    else
      let body = cons_body dq.head dq.body in
      { dq with body; head = arr }

  (*
      The logic for snoc is the inverse of the logic for cons.

      If we can add this element to the current tail while staying under the target length,
      then do so.

      Else, if the body is empty and the head is also empty, then set the current tail as the new head
      and the new element as the tail.

      Else, snoc the current tail to the body and set the new element as the tail.
  *)
  let snoc el dq =
    if Array.length dq.tail < target_length then
      let tail = Array.append dq.tail [| el |] in
      { dq with tail }
    else if is_body_empty dq.body && Array.length dq.head = 0 then
      let head = dq.tail in
      { dq with tail = [| el |]; head }
    else
      let body = snoc_body dq.tail dq.body in
      let tail = [| el |] in
      { dq with body; tail }

  let snoc_many arr dq =
    if is_less_than_target dq.tail arr then
      let tail = Array.append dq.tail arr in
      { dq with tail }
    else if is_body_empty dq.body && Array.length dq.head = 0 then
      let head = dq.tail in
      { dq with tail = arr; head }
    else
      let body = snoc_body dq.tail dq.body in
      { dq with body; tail = arr }

  (*
      Access to the front or back is simple.
      For the front: if the head is not empty, then return the first element in the head.
      Else, return the first element in the tail if the tail contains any, or return None.

      The insertion logic above that takes the deque (not the body) should guarantee
      that the head and tail are full before inserting into the body.
      So there is no need to check the body to return the front element.
  *)
  let front dq =
    if Array.length dq.head > 0 then Some (Array.unsafe_get dq.head 0)
    else if Array.length dq.tail > 0 then Some (Array.unsafe_get dq.tail 0)
    else None

  (*
      Simple inverse of logic for front: 
      Check if there are any elements in the tail and return the last if so;
      else return the last element in the head if there are any, or return None. 
   *)
  let back dq =
    if Array.length dq.tail > 0 then
      Some (Array.unsafe_get dq.tail (Array.length dq.tail - 1))
    else if Array.length dq.head > 0 then
      Some (Array.unsafe_get dq.head (Array.length dq.head - 1))
    else None

  (*
      There are a few cases we want to handle when it comes to removal from the front.

      If there is more than one element in the head, we can simple remove that from the array.
      If there is just one element in the head, we want to pop the leftmost array in the body
      and use that as the head for O(1) access to the front.
      If the head is empty, then the body must also be empty, 
      and in that case we must check if the tail is empty and remove the first element from the tail
      if it contains any elements, or else return the empty deque if the tail is also empty.
   *)
  let remove_front dq =
    if Array.length dq.head > 1 then
      let head = Array.sub dq.head 1 (Array.length dq.head - 1) in
      { dq with head }
    else if Array.length dq.head = 1 then
      let body, head = pop_body_start dq.body in
      { dq with head; body }
    else if Array.length dq.tail > 0 then
      let tail = Array.sub dq.tail 1 (Array.length dq.tail - 1) in
      { dq with tail }
    else dq

  (*
      Logic for removing from the back is the inverse of the logic for removing from the front.

      If there is more than one element in the tail, remove last element in the array.
      If there is just one element in the tail, pop the rightmost array in the body
      and use that has the tail.
      Else, remove last element in the head if the head contains any elements, or return empty deque.
   *)
  let remove_back dq =
    if Array.length dq.tail > 1 then
      let tail = Array.sub dq.tail 0 (Array.length dq.tail - 1) in
      { dq with tail }
    else if Array.length dq.tail = 1 then
      let body, tail = pop_body_end dq.body in
      { dq with body; tail }
    else if Array.length dq.head > 0 then
      let head = Array.sub dq.head 0 (Array.length dq.head - 1) in
      { dq with head }
    else dq

  (*
      Logic for get_at is simple.
      Is the idx requested less than 0? Then return None because the idx doesn't exist.
      Is the idx requested less than the length of the head? Then get the element from the head.
      Is the idx requested less than the length of the body? Then get the element from the body,
      subtracting the idx from the head length for proper retrieval.
      Is the idx requested less than the length of the tail? Then get the element from the tail.
      Else, the idx requested doesn't exist so return None.
   *)
  let get_at idx dq =
    if idx < 0 then None
    else if idx < Array.length dq.head then Some (Array.unsafe_get dq.head idx)
    else
      let body_length = size_body dq.body in
      if idx < body_length + Array.length dq.head then
        let idx = idx - Array.length dq.head in
        get_at_body idx dq.body
      else
        let idx = idx - (Array.length dq.head + body_length) in
        if idx < Array.length dq.tail then Some (Array.unsafe_get dq.tail idx)
        else None

  (*
    This function helps with inserting into the head.
    Inserting into the head is simple, but it's complicated by the fact that,
    if the user inserts more than target_length elements into the head using
    cons_many, we want to keep the array smaller than target_length,
    and have to do some splitting.
    The exact kind of splitting depends on if either of the two subarrays
    are less than target_length. 
    If one of them is, then add the current element to that array,
    but if neither is, then insert the current element into the body 
    as an array containing just one element.
   *)
  let insert_when_head_is_too_large sub1 el sub2 dq =
    if Array.length sub1 + 1 < target_length then
      let body = cons_body sub2 dq.body in
      let head = Array.append sub1 [| el |] in
      { dq with head; body }
    else if Array.length sub2 + 1 < target_length then
      let sub2 = Array.append [| el |] sub2 in
      let body = cons_body sub2 dq.body in
      { dq with head = sub1; body }
    else
      let body = cons_body sub2 dq.body in
      let body = cons_body [| el |] body in
      { dq with head = sub1; body }

  (*
      This function helps with inserting into the head array.
      It handles the simple and common case when the array is less than target_length,
      and calls another function to insert when the array is not less than that.
  *)
  let insert_into_head idx el dq =
    let sub1 = Array.sub dq.head 0 idx in
    let sub2_len = Array.length dq.head - idx in
    let sub2 = Array.sub dq.head idx sub2_len in
    if Array.length sub1 + Array.length sub2 + 1 < target_length then
      let head = Array.concat [ sub1; [| el |]; sub2 ] in
      { dq with head }
    else insert_when_head_is_too_large sub1 el sub2 dq

  (*
      Same as insert_when_head_is_too_large function except it deals with the tail.
   *)
  let insert_when_tail_is_too_large sub1 el sub2 dq =
    if Array.length sub1 + 1 < target_length then
      let body = snoc_body sub2 dq.body in
      let tail = Array.append sub1 [| el |] in
      { dq with tail; body }
    else if Array.length sub2 + 1 < target_length then
      let sub2 = Array.append [| el |] sub2 in
      let body = snoc_body sub2 dq.body in
      { dq with tail = sub1; body }
    else
      let body = snoc_body sub2 dq.body in
      let body = snoc_body [| el |] body in
      { dq with tail = sub1; body }

  (*
    Same as insert_into_head function except it deals with the tail,
    and it also changes the index offset the user provided to index into the tail.

    The total length of the structure and the one that the user thinks of
    and provided an index for is:
      head_length + body_length + tail_length.
    
    When we want to index into the tail, we subtract head_length and body_length from the index
    and that will give us an appropriate offset we can use for the tail.
  *)
  let insert_into_tail before_tail idx el dq =
    let idx = idx - before_tail in
    let sub1 = Array.sub dq.tail 0 idx in
    let sub2_len = Array.length dq.tail - idx in
    let sub2 = Array.sub dq.tail idx sub2_len in
    if Array.length sub1 + Array.length sub2 + 1 < target_length then
      let tail = Array.concat [ sub1; [| el |]; sub2 ] in
      { dq with tail }
    else insert_when_tail_is_too_large sub1 el sub2 dq

  (* Inserts an element at any location in the deque. *)
  let insert_at idx el dq =
    if idx <= 0 then cons el dq
    else if idx < Array.length dq.head then insert_into_head idx el dq
    else
      let body_size = size_body dq.body in
      let before_tail = body_size + Array.length dq.head in
      if idx < before_tail then
        let body =
          insert_at_body (idx - Array.length dq.head) [| el |] dq.body
        in
        { dq with body }
      else
        let after_tail = before_tail + Array.length dq.tail in
        if idx >= after_tail then snoc el dq
        else insert_into_tail before_tail idx el dq

  (*
    Removes the element at the index in the head.
    The noteworthy things are: (a) how the first node in the body is popped
    if the head has only one element (to guarantee O(1) access),
    and (b) how, if the array is larger than the target length, part of the array
    that was at the head is consed to the body.
   *)
  let remove_from_head idx dq =
    if Array.length dq.head = 1 then
      let body, head = pop_body_start dq.body in
      { dq with head; body }
    else if idx = 0 then
      let head = Array.sub dq.head 1 (Array.length dq.head - 1) in
      { dq with head }
    else if idx = Array.length dq.head - 1 then
      let head = Array.sub dq.head 0 (Array.length dq.head - 1) in
      { dq with head }
    else
      let sub1 = Array.sub dq.head 0 idx in
      let sub2_len = Array.length dq.head - idx in
      let sub2 = Array.sub dq.head idx sub2_len in
      if is_less_than_target sub1 sub2 then
        let head = Array.append sub1 sub2 in
        { dq with head }
      else
        let body = cons_body sub2 dq.body in
        { dq with head = sub1; body }

  let remove_from_tail idx dq =
    if Array.length dq.tail = 1 then
      let body, tail = pop_body_end dq.body in
      { dq with body; tail }
    else if idx = 0 then
      let tail = Array.sub dq.tail 1 (Array.length dq.tail - 1) in
      { dq with tail }
    else if idx = Array.length dq.tail - 1 then
      let tail = Array.sub dq.tail 0 (Array.length dq.tail - 1) in
      { dq with tail }
    else
      let sub1 = Array.sub dq.tail 0 idx in
      let sub2_len = Array.length dq.tail - idx in
      let sub2 = Array.sub dq.tail idx sub2_len in
      if is_less_than_target sub1 sub2 then
        let tail = Array.append sub1 sub2 in
        { dq with tail }
      else
        let body = snoc_body sub1 dq.body in
        { dq with tail = sub2; body }

  let remove_at idx dq =
    if idx < 0 then dq
    else if idx < Array.length dq.head then remove_from_head idx dq
    else
      let body_size = size_body dq.body in
      let before_tail = body_size + Array.length dq.head in
      if idx < before_tail then
        let body = del_at_body (idx - Array.length dq.head) dq.body in
        { dq with body }
      else remove_from_tail (idx - before_tail) dq

  let map f dq =
    let head = Array.map f dq.head in
    let tail = Array.map f dq.tail in
    let body = map_body f dq.body in
    { head; tail; body }

  let fold_left f acc dq =
    let acc = Array.fold_left f acc dq.head in
    let acc = fold_left_body f acc dq.body in
    Array.fold_left f acc dq.tail

  let fold_right f acc dq =
    let acc = Array.fold_right f dq.tail acc in
    let acc = fold_right_body f acc dq.body in
    Array.fold_right f dq.head acc
end
