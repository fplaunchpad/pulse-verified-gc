(* t09_small_sizes.ml
   Target: the smallest block sizes.
   A free block needs one word for its header and one for the next
   pointer. So a one-word block is the boundary case for free list
   linking. The allocator refuses to split when the remainder would be
   under two words, which is what keeps zero-size blocks from arising.
   This exercises that boundary repeatedly. *)

let () =
  (* many one and two word objects, freed in a pattern that leaves small holes *)
  let keep = Array.make 20000 [||] in
  for i = 0 to 19999 do
    keep.(i) <- Array.make (1 + i mod 3) i
  done;
  for i = 0 to 19999 do
    if i mod 3 <> 0 then keep.(i) <- [||]
  done;

  for _ = 1 to 5000 do
    ignore (Array.make 1 0);
    ignore (Array.make 2 0)
  done;

  let s = Array.fold_left (fun a x -> a + Array.length x) 0 keep in
  Printf.printf "s=%d\n" s;
  Printf.printf "t09 ok\n"
